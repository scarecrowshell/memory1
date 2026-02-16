// memory_core_cli.c
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <uuid/uuid.h>
#include <openssl/sha.h>
#include <dirent.h>
#include <unistd.h>
#include <stdint.h>
#include <limits.h>

#ifndef PATH_MAX
#define PATH_MAX 4096
#endif

#define DEFAULT_BASE_DIR "memory_store"
#define DEFAULT_RETENTION_DAYS 7
#define DEFAULT_MAX_SCANS 5000

static void *xmalloc(size_t n) { void *p = malloc(n); if (!p) { perror("malloc"); exit(1); } return p; }
static char *xstrdup(const char *s) { char *r = strdup(s); if (!r) { perror("strdup"); exit(1); } return r; }

static int mkdirs(const char *path, mode_t mode) {
    char tmp[PATH_MAX];
    snprintf(tmp, sizeof(tmp), "%s", path);
    size_t len = strlen(tmp);
    if (len == 0) return -1;
    if (tmp[len-1] == '/') tmp[len-1] = 0;
    for (char *p = tmp + 1; *p; ++p) {
        if (*p == '/') {
            *p = 0;
            if (mkdir(tmp, mode) && errno != EEXIST) return -1;
            *p = '/';
        }
    }
    if (mkdir(tmp, mode) && errno != EEXIST) return -1;
    return 0;
}

static int write_file(const char *path, const char *buf, size_t len) {
    FILE *f = fopen(path, "w");
    if (!f) return -1;
    if (len > 0) {
        if (fwrite(buf, 1, len, f) != len) { fclose(f); return -1; }
    }
    fclose(f);
    return 0;
}

static int rm_rf(const char *path) {
    struct stat st;
    if (lstat(path, &st) == -1) return -1;
    if (S_ISDIR(st.st_mode)) {
        DIR *d = opendir(path);
        if (!d) return -1;
        struct dirent *entry;
        char child[PATH_MAX];
        while ((entry = readdir(d)) != NULL) {
            if (!strcmp(entry->d_name, ".") || !strcmp(entry->d_name, "..")) continue;
            snprintf(child, sizeof(child), "%s/%s", path, entry->d_name);
            rm_rf(child);
        }
        closedir(d);
        if (rmdir(path) == -1) return -1;
    } else {
        if (unlink(path) == -1) return -1;
    }
    return 0;
}

/* Read stdin fully into dynamically allocated buffer. Returns pointer and sets len */
static char *read_stdin(size_t *out_len) {
    size_t cap = 65536;
    size_t len = 0;
    char *buf = xmalloc(cap + 1);
    ssize_t r;
    while ((r = fread(buf + len, 1, cap - len, stdin)) > 0) {
        len += r;
        if (cap - len == 0) {
            cap *= 2;
            buf = realloc(buf, cap + 1);
            if (!buf) { perror("realloc"); exit(1); }
        }
    }
    buf[len] = '\0';
    if (out_len) *out_len = len;
    return buf;
}

/* compute sha256 hex of buffer */
static char *sha256_hex_buf(const unsigned char *data, size_t len) {
    unsigned char hash[SHA256_DIGEST_LENGTH];
    SHA256(data, len, hash);
    char *hex = xmalloc(SHA256_DIGEST_LENGTH*2 + 1);
    for (int i = 0; i < SHA256_DIGEST_LENGTH; ++i) {
        sprintf(hex + (i*2), "%02x", hash[i]);
    }
    hex[SHA256_DIGEST_LENGTH*2] = 0;
    return hex;
}

/* Structure for scan directory info for cleanup */
typedef struct {
    char *path;
    time_t mtime;
} scan_entry_t;

/* Recursively collect scan directories containing metadata.json under base_dir.
   A scan dir is identified by presence of metadata.json or normalized.json */
/* The function fills entries_count and returns an allocated array (free each path and array) */
static scan_entry_t *collect_scan_dirs(const char *base_dir, size_t *entries_count) {
    scan_entry_t *arr = NULL;
    size_t cap = 0, cnt = 0;

    /* walk base_dir recursively */
    DIR *d = opendir(base_dir);
    if (!d) { *entries_count = 0; return NULL; }

    struct dirent *e;
    char path[PATH_MAX];

    /* stack for directories to traverse */
    typedef struct {
        char *dpath;
    } stack_item;
    stack_item *stack = NULL;
    size_t stack_cap = 0, stack_cnt = 0;

    /* push base_dir */
    stack_cap = 16;
    stack = xmalloc(stack_cap * sizeof(stack_item));
    stack[stack_cnt++].dpath = xstrdup(base_dir);

    while (stack_cnt > 0) {
        char *cur = stack[--stack_cnt].dpath;
        DIR *cd = opendir(cur);
        if (!cd) { free(cur); continue; }
        while ((e = readdir(cd)) != NULL) {
            if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
            snprintf(path, sizeof(path), "%s/%s", cur, e->d_name);
            struct stat st;
            if (lstat(path, &st) == -1) continue;
            if (S_ISDIR(st.st_mode)) {
                /* push directory */
                if (stack_cnt == stack_cap) {
                    stack_cap *= 2;
                    stack = realloc(stack, stack_cap * sizeof(stack_item));
                    if (!stack) { perror("realloc"); exit(1); }
                }
                stack[stack_cnt++].dpath = xstrdup(path);
            } else {
                /* check for metadata.json or normalized.json in this directory by looking up */
            }
        }
        closedir(cd);

        /* Now check if cur contains metadata.json or normalized.json */
        char meta_path[PATH_MAX];
        snprintf(meta_path, sizeof(meta_path), "%s/metadata.json", cur);
        struct stat mst;
        if (stat(meta_path, &mst) == 0) {
            /* found a scan dir */
            if (cnt == cap) {
                cap = (cap == 0) ? 64 : cap * 2;
                arr = realloc(arr, cap * sizeof(scan_entry_t));
                if (!arr) { perror("realloc"); exit(1); }
            }
            arr[cnt].path = xstrdup(cur);
            arr[cnt].mtime = mst.st_mtime;
            cnt++;
        } else {
            /* also accept presence of normalized.json */
            char norm_path[PATH_MAX];
            snprintf(norm_path, sizeof(norm_path), "%s/normalized.json", cur);
            if (stat(norm_path, &mst) == 0) {
                if (cnt == cap) {
                    cap = (cap == 0) ? 64 : cap * 2;
                    arr = realloc(arr, cap * sizeof(scan_entry_t));
                    if (!arr) { perror("realloc"); exit(1); }
                }
                arr[cnt].path = xstrdup(cur);
                arr[cnt].mtime = mst.st_mtime;
                cnt++;
            }
        }

        free(cur);
    }

    for (size_t i = 0; i < stack_cnt; ++i) free(stack[i].dpath);
    free(stack);

    *entries_count = cnt;
    return arr;
}

/* Comparator for qsort by mtime ascending */
static int cmp_scan_entry(const void *a, const void *b) {
    const scan_entry_t *A = (const scan_entry_t *)a;
    const scan_entry_t *B = (const scan_entry_t *)b;
    if (A->mtime < B->mtime) return -1;
    if (A->mtime > B->mtime) return 1;
    return 0;
}

/* Perform retention cleanup:
   - Delete entries older than retention_days (if retention_days > 0)
   - Enforce max_scans (if max_scans > 0)
*/
static void perform_retention(const char *base_dir, int retention_days, int max_scans) {
    size_t cnt = 0;
    scan_entry_t *entries = collect_scan_dirs(base_dir, &cnt);
    if (!entries || cnt == 0) {
        free(entries);
        return;
    }

    qsort(entries, cnt, sizeof(scan_entry_t), cmp_scan_entry);

    time_t now = time(NULL);
    ssize_t removed = 0;

    if (retention_days > 0) {
        time_t cutoff = now - (time_t)retention_days * 86400L;
        for (size_t i = 0; i < cnt; ++i) {
            if (entries[i].mtime < cutoff) {
                rm_rf(entries[i].path);
                removed++;
                free(entries[i].path);
                entries[i].path = NULL;
            } else {
                /* since sorted ascending, once we hit >= cutoff, break */
                break;
            }
        }
    }

    /* compact remaining entries */
    size_t kept = 0;
    for (size_t i = 0; i < cnt; ++i) {
        if (entries[i].path) {
            entries[kept++] = entries[i];
        }
    }
    cnt = kept;

    if (max_scans > 0 && (ssize_t)cnt > max_scans) {
        ssize_t to_remove = (ssize_t)cnt - max_scans;
        for (ssize_t i = 0; i < to_remove; ++i) {
            rm_rf(entries[i].path);
            free(entries[i].path);
            entries[i].path = NULL;
            removed++;
        }
    }

    /* free remaining */
    for (size_t i = 0; i < cnt; ++i) {
        if (entries[i].path) free(entries[i].path);
    }
    free(entries);
}

/* Minimal argument parsing */
static void print_usage(const char *prog) {
    fprintf(stderr,
        "Usage: %s [--host HOST] [--type TYPE] [--severity N] [--base-dir DIR] [--retention-days N] [--max-scans N]\n",
        prog);
}

/* Main program */
int main(int argc, char **argv) {
    const char *host = "localhost";
    const char *scan_type = "generic";
    int severity = 0;
    char base_dir[PATH_MAX];
    strncpy(base_dir, DEFAULT_BASE_DIR, sizeof(base_dir));
    int retention_days = DEFAULT_RETENTION_DAYS;
    int max_scans = DEFAULT_MAX_SCANS;

    for (int i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--host") && i + 1 < argc) { host = argv[++i]; }
        else if (!strcmp(argv[i], "--type") && i + 1 < argc) { scan_type = argv[++i]; }
        else if (!strcmp(argv[i], "--severity") && i + 1 < argc) { severity = atoi(argv[++i]); }
        else if (!strcmp(argv[i], "--base-dir") && i + 1 < argc) { strncpy(base_dir, argv[++i], sizeof(base_dir)-1); base_dir[sizeof(base_dir)-1]=0; }
        else if (!strcmp(argv[i], "--retention-days") && i + 1 < argc) { retention_days = atoi(argv[++i]); }
        else if (!strcmp(argv[i], "--max-scans") && i + 1 < argc) { max_scans = atoi(argv[++i]); }
        else if (!strcmp(argv[i], "--help")) { print_usage(argv[0]); return 0; }
        else { print_usage(argv[0]); return 1; }
    }

    size_t stdin_len = 0;
    char *stdin_buf = read_stdin(&stdin_len);
    if (!stdin_buf || stdin_len == 0) {
        fprintf(stderr, "No input on stdin\n");
        free(stdin_buf);
        return 1;
    }

    char *norm_buf = stdin_buf; /* treat normalized == stdin for this simple CLI */
    size_t norm_len = stdin_len;

    char *hash = sha256_hex_buf((unsigned char*)norm_buf, norm_len);

    /* create uuid and directory */
    uuid_t u;
    uuid_generate(u);
    char uuid_str[37];
    uuid_unparse_lower(u, uuid_str);

    time_t now = time(NULL);
    struct tm tm;
    gmtime_r(&now, &tm);
    char date_path[128];
    strftime(date_path, sizeof(date_path), "%Y/%m/%d", &tm);

    char full_dir[PATH_MAX];
    snprintf(full_dir, sizeof(full_dir), "%s/%s/%s", base_dir, date_path, uuid_str);

    if (mkdirs(full_dir, 0755) != 0) {
        fprintf(stderr, "Failed create dir %s: %s\n", full_dir, strerror(errno));
        free(hash);
        free(stdin_buf);
        return 1;
    }

    char raw_path[PATH_MAX], norm_path[PATH_MAX], meta_path[PATH_MAX], hash_path[PATH_MAX];
    snprintf(raw_path, sizeof(raw_path), "%s/raw.json", full_dir);
    snprintf(norm_path, sizeof(norm_path), "%s/normalized.json", full_dir);
    snprintf(meta_path, sizeof(meta_path), "%s/metadata.json", full_dir);
    snprintf(hash_path, sizeof(hash_path), "%s/hash.txt", full_dir);

    if (write_file(raw_path, stdin_buf, stdin_len) != 0) {
        fprintf(stderr, "Failed write raw\n");
        rm_rf(full_dir);
        free(hash);
        free(stdin_buf);
        return 1;
    }
    if (write_file(norm_path, norm_buf, norm_len) != 0) {
        fprintf(stderr, "Failed write norm\n");
        rm_rf(full_dir);
        free(hash);
        free(stdin_buf);
        return 1;
    }

    FILE *fm = fopen(meta_path, "w");
    if (fm) {
        fprintf(fm, "{ \"host\": \"%s\", \"scan_type\": \"%s\", \"timestamp\": %ld, \"severity\": %d }\n",
                host, scan_type, (long)now, severity);
        fclose(fm);
    }

    FILE *fh = fopen(hash_path, "w");
    if (fh) { fputs(hash, fh); fputc('\n', fh); fclose(fh); }

    free(hash);
    free(stdin_buf);

    /* perform retention cleanup */
    perform_retention(base_dir, retention_days, max_scans);

    return 0;
}
