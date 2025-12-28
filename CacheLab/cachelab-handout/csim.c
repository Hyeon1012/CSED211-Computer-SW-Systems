#include <getopt.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include "cachelab.h"

int s = 0, E = 0, b = 0;
char* trace_file = NULL;
int verbose = 0;
int hit_count = 0, miss_count = 0, eviction_count = 0;
unsigned int global_timer = 0;

typedef struct {
    int valid;
    unsigned long long tag;
    unsigned int last_access;
} CacheLine;

typedef struct {
    CacheLine* lines;
} CacheSet;

typedef struct {
    CacheSet* sets;
} Cache;

Cache cache;

void allocateCache() {
    int S = (1 << s);
    cache.sets = (CacheSet*)malloc(sizeof(CacheSet) * S);
    for (int i = 0; i < S; i++) {
        cache.sets[i].lines = (CacheLine*)malloc(sizeof(CacheLine) * E);
        for (int j = 0; j < E; j++) {
            cache.sets[i].lines[j].valid = 0;
            cache.sets[i].lines[j].tag = 0;
            cache.sets[i].lines[j].last_access = 0;
        }
    }
}

void freeCache() {
    int S = (1 << s);
    for (int i = 0; i < S; i++) free(cache.sets[i].lines);
    free(cache.sets);
}

void accessCache(unsigned long long address) {
    unsigned long long set_index = (address >> b) & ((1 << s) - 1);
    unsigned long long tag = address >> (s + b);
    CacheSet* set = &cache.sets[set_index];

    global_timer++;
    int empty = -1, lru = 0;
    unsigned int min_time = -1;

    for (int i = 0; i < E; i++) {
        if (set->lines[i].valid) {
            if (set->lines[i].tag == tag) { // Hit
                hit_count++;
                set->lines[i].last_access = global_timer;
                if (verbose) printf(" hit");
                return;
            }
            if (set->lines[i].last_access < min_time) { // LRU 찾기
                min_time = set->lines[i].last_access;
                lru = i;
            }
        }
        else if (empty == -1) {
            empty = i; // 빈 공간 찾기
        }
    }

    miss_count++; // Miss
    if (verbose) printf(" miss");

    int target = (empty != -1) ? empty : lru;
    if (empty == -1) {
        eviction_count++; // Eviction
        if (verbose) printf(" eviction");
    }

    set->lines[target].valid = 1;
    set->lines[target].tag = tag;
    set->lines[target].last_access = global_timer;
}

void help() {
    printf("Usage: ./csim [-hv] -s <num> -E <num> -b <num> -t <file>\n");
    printf("Options:\n");
    printf("  -h         Print this help message.\n");
    printf("  -v         Optional verbose flag.\n");
    printf("  -s <num>   Number of set index bits.\n");
    printf("  -E <num>   Number of lines per set.\n");
    printf("  -b <num>   Number of block offset bits.\n");
    printf("  -t <file>  Trace file.\n");
    printf("\n");
    printf("Examples:\n");
    printf("  linux>  ./csim -s 4 -E 1 -b 4 -t traces/yi.trace\n");
    printf("  linux>  ./csim -v -s 8 -E 2 -b 4 -t traces/yi.trace\n");
}

int main(int argc, char* argv[]) {
    char opt;
    while ((opt = getopt(argc, argv, "hvs:E:b:t:")) != -1) {
        switch (opt) {
        case 'h': help(); exit(1); break;
        case 'v': verbose = 1; break;
        case 's': s = atoi(optarg); break;
        case 'E': E = atoi(optarg); break;
        case 'b': b = atoi(optarg); break;
        case 't': trace_file = optarg; break;
        default: exit(1); // 잘못된 인자 들어오면 그냥 종료
        }
    }

    if (s == 0 || E == 0 || b == 0 || trace_file == NULL) {
        printf("Missing arguments\n"); // 필수 인자 없으면 메시지 띄우고 종료
        exit(1);
    }

    allocateCache();

    FILE* pFile = fopen(trace_file, "r");
    if (!pFile) return 1;

    char op;
    unsigned long long addr;
    int size;

    while (fscanf(pFile, " %c %llx,%d", &op, &addr, &size) > 0) {
        if (op == 'I') continue;
        if (verbose) printf("%c %llx,%d", op, addr, size);

        accessCache(addr);
        if (op == 'M') accessCache(addr); // M은 한 번 더 접근

        if (verbose) printf("\n");
    }

    fclose(pFile);
    freeCache();
    printSummary(hit_count, miss_count, eviction_count);
    return 0;
}