/* Copyright @2012 by Justin Hines at Bitly under a very liberal license. See LICENSE in the source distribution. */

#define _GNU_SOURCE
#include <sys/stat.h>
#include <stdint.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <fcntl.h>
#include <math.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#include "city.h"
#include "dablooms.h"

#define DABLOOMS_VERSION "0.8.1"

#define DABLOOMS_HASH64(ptr, len, seed) CityHash64WithSeed(ptr, len, seed)
#define HEADER_BYTES (2*sizeof(uint32_t))
#define SCALE_HEADER_BYTES (3*sizeof(uint64_t))

const char *dablooms_version(void)
{
    return DABLOOMS_VERSION;
}

void free_bitmap(bitmap_t *bitmap)
{
    if ((munmap(bitmap->array, bitmap->bytes)) < 0) {
        perror("Error, unmapping memory");
    }
    close(bitmap->fd);
    free(bitmap);
}

bitmap_t *bitmap_resize(bitmap_t *bitmap, size_t old_size, size_t new_size)
{
    int fd = bitmap->fd;
    struct stat fileStat;
    
    fstat(fd, &fileStat);
    size_t size = fileStat.st_size;
    
    /* Write something to the end of the file to insure allocated the space */
    if (size == old_size) {
		if (lseek(fd, new_size, SEEK_SET) < 0 ||
			ftruncate(fd, (off_t)new_size) < 0) {
			perror("Error increasing file size with ftruncate");
			free_bitmap(bitmap);
			close(fd);
			return NULL;
		}
    }
    lseek(fd, 0, SEEK_SET);
    
    /* resize if mmap exists and possible on this os, else new mmap */
    if (bitmap->array != NULL) {
#if __linux
        bitmap->array = mremap(bitmap->array, old_size, new_size, MREMAP_MAYMOVE);
        if (bitmap->array == MAP_FAILED) {
            perror("Error resizing mmap");
            free_bitmap(bitmap);
            close(fd);
            return NULL;
        }
#else
        if (munmap(bitmap->array, bitmap->bytes) < 0) {
            perror("Error unmapping memory");
            free_bitmap(bitmap);
            close(fd);
            return NULL;
        }
        bitmap->array = NULL;
#endif
    }
    if (bitmap->array == NULL) {
        bitmap->array = mmap(0, new_size, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
        if (bitmap->array == MAP_FAILED) {
            perror("Error init mmap");
            free_bitmap(bitmap);
            close(fd);
            return NULL;
        }
    }
    
    bitmap->bytes = new_size;
    return bitmap;
}

/* Create a new bitmap, not full featured, simple to give
 * us a means of interacting with the 4 bit counters */
bitmap_t *new_bitmap(int fd, size_t bytes)
{
    bitmap_t *bitmap;
    
    if ((bitmap = (bitmap_t *)malloc(sizeof(bitmap_t))) == NULL) {
        return NULL;
    }
    
    bitmap->bytes = bytes;
    bitmap->fd = fd;
    bitmap->array = NULL;
    
    if ((bitmap = bitmap_resize(bitmap, 0, bytes)) == NULL) {
        return NULL;
    }
    
    return bitmap;
}

int bitmap_increment(bitmap_t *bitmap, unsigned int index, unsigned int offset)
{
    uint32_t access = index / 2 + offset;
    uint8_t temp;
    uint8_t n = bitmap->array[access];
    if (index % 2 != 0) {
        temp = (n & 0x0f);
        n = (n & 0xf0) + ((n & 0x0f) + 0x01);
    } else {
        temp = (n & 0xf0) >> 4;
        n = (n & 0x0f) + ((n & 0xf0) + 0x10);
    }
    
    if (temp == 0x0f) {
        fprintf(stderr, "Error, 4 bit int Overflow\n");
        return -1;
    }
    
    bitmap->array[access] = n;
    return 0;
}

/* increments the four bit counter */
int bitmap_decrement(bitmap_t *bitmap, unsigned int index, unsigned int offset)
{
    uint32_t access = index / 2 + offset;
    uint32_t temp;
    uint32_t n = bitmap->array[access];
    
    if (index % 2 != 0) {
        temp = (n & 0x0f);
        n = (n & 0xf0) + ((n & 0x0f) - 0x01);
    } else {
        temp = (n & 0xf0) >> 4;
        n = (n & 0x0f) + ((n & 0xf0) - 0x10);
    }
    
    if (temp == 0x00) {
        fprintf(stderr, "Error, Decrementing zero\n");
        return -1;
    }
    
    bitmap->array[access] = n;
    return 0;
}

/* decrements the four bit counter */
int bitmap_check(bitmap_t *bitmap, unsigned int index, unsigned int offset)
{
    unsigned int access = index / 2 + offset;
    if (index % 2 != 0 ) {
        return bitmap->array[access] & 0x0f;
    } else {
        return bitmap->array[access] & 0xf0;
    }
}

int bitmap_flush(bitmap_t *bitmap)
{
    if ((msync(bitmap->array, bitmap->bytes, MS_SYNC) < 0)) {
        perror("Error, flushing bitmap to disk");
        return -1;
    } else {
        return 0;
    }
}

static void new_salts(counting_bloom_t *bloom)
{
	const uint64_t root = 0xd32463a2ba01742cLL;
	const uint64_t seed = 0x4fb95f06d3702acbLL;
    int i, num_salts = bloom->nfuncs / 2;
    
    if (bloom->nfuncs % 2)
        num_salts++;

	bloom->salts = calloc(num_salts, sizeof(uint64_t));
	bloom->salts[0] = DABLOOMS_HASH64((char *)&root, sizeof(uint64_t), seed);

    for (i = 1; i < num_salts; i++) {
		uint64_t base = bloom->salts[i - 1] ^ i;
		bloom->salts[i] = DABLOOMS_HASH64((char *)&base, sizeof(uint64_t), seed);
    }
}

static void hash_func(counting_bloom_t *bloom, const char *key, size_t key_len, uint32_t *hashes)
{
	int i, num_salts = bloom->nfuncs / 2;
	uint64_t *h = (uint64_t *)hashes;

	for (i = 0; i < num_salts; ++i) {
		h[i] = DABLOOMS_HASH64(key, key_len, bloom->salts[i]);
	}

	if (bloom->nfuncs % 2) {
		uint32_t hash = (uint32_t)DABLOOMS_HASH64(key, key_len, bloom->salts[num_salts]);
		hashes[bloom->nfuncs - 1] = hash;
	}

	for (i = 0; i < bloom->nfuncs; ++i)
		hashes[i] = hashes[i] % bloom->counts_per_func;
}

int free_counting_bloom(counting_bloom_t *bloom)
{
    if (bloom != NULL) {
        free(bloom->header);
        bloom->header = NULL;
        
        free(bloom->salts);
        bloom->salts = NULL;
        
        free(bloom->hashes);
        bloom->hashes = NULL;
        
        free(bloom);
        bloom = NULL;
    }
    return 0;
}

counting_bloom_t *counting_bloom_init(unsigned int capacity, double error_rate,
                                      unsigned int offset, uint32_t id, unsigned int count)
{
    counting_bloom_t *bloom;
    
    if ((bloom = malloc(sizeof(counting_bloom_t))) == NULL) {
        fprintf(stderr, "Error, could not realloc a new bloom filter\n");
        return NULL;
    }
    if ((bloom->header = malloc(sizeof(counting_bloom_header_t))) == NULL) {
        fprintf(stderr, "Error, could not malloc size for pointers of headers\n");
        return NULL;
    }
    bloom->salts = NULL;
    bloom->parent_bitmap = NULL;
    bloom->capacity = capacity;
    bloom->error_rate = error_rate;
    bloom->offset = offset + HEADER_BYTES;
    bloom->nfuncs = (int) ceil(log(1 / error_rate) / log(2));
    bloom->counts_per_func = (int) ceil(capacity * fabs(log(error_rate)) / (bloom->nfuncs * pow(log(2), 2)));
    bloom->size = ceil(bloom->nfuncs * bloom->counts_per_func);
    bloom->num_bytes = (int) ceil(bloom->size / 2 + HEADER_BYTES);
    bloom->hashes = calloc(bloom->nfuncs, sizeof(unsigned int));
    new_salts(bloom);
    
    return bloom;
}

counting_bloom_t *new_counting_bloom(unsigned int capacity, double error_rate, const char *filename)
{
    counting_bloom_t *cur_bloom;
    int fd;
    
    if ((fd = open(filename, O_RDWR | O_CREAT | O_TRUNC, (mode_t)0600)) < 0) {
        perror("Error, Opening File Failed");
        fprintf(stderr, " %s \n", filename);
        return NULL;
    }
    
    cur_bloom = counting_bloom_init(capacity, error_rate, 0, 0, 0);
    cur_bloom->parent_bitmap = new_bitmap(fd, cur_bloom->num_bytes);
    
    return cur_bloom;
}

counting_bloom_t *counting_bloom_from_file(unsigned capacity, double error_rate, const char *filename)
{
    counting_bloom_t *cur_bloom;
    int fd;
    
    if ((fd = open(filename, O_RDWR, (mode_t)0600)) < 0) {
        perror("Error, Opening File Failed");
        fprintf(stderr, " %s \n", filename);
        return NULL;
    }
    
    cur_bloom = counting_bloom_init(capacity, error_rate, 0, 0, 0);
    cur_bloom->parent_bitmap = new_bitmap(fd, cur_bloom->num_bytes);
    
    return cur_bloom;
}

int counting_bloom_add(counting_bloom_t *bloom, const char *s, size_t len)
{
    unsigned int index, i, offset;
    unsigned int *hashes = bloom->hashes;
    
    hash_func(bloom, s, len, hashes);
    
    for (i = 0; i < bloom->nfuncs; i++) {
        offset = i * bloom->counts_per_func;
        index = hashes[i] + offset;
        bitmap_increment(bloom->parent_bitmap, index, bloom->offset);
    }
    (*bloom->header->count)++;
    
    return 0;
}

int counting_bloom_remove(counting_bloom_t *bloom, const char *s, size_t len)
{
    unsigned int index, i, offset;
    unsigned int *hashes = bloom->hashes;
    
    hash_func(bloom, s, len, hashes);
    
    for (i = 0; i < bloom->nfuncs; i++) {
        offset = i * bloom->counts_per_func;
        index = hashes[i] + offset;
        bitmap_decrement(bloom->parent_bitmap, index, bloom->offset);
    }
    (*bloom->header->count)--;
    
    return 0;
}

int counting_bloom_check(counting_bloom_t *bloom, const char *s, size_t len)
{
    unsigned int index, i, offset;
    unsigned int *hashes = bloom->hashes;
    
    hash_func(bloom, s, len, hashes);
    
    for (i = 0; i < bloom->nfuncs; i++) {
        offset = i * bloom->counts_per_func;
        index = hashes[i] + offset;
        if (!(bitmap_check(bloom->parent_bitmap, index, bloom->offset))) {
            return 0;
        }
    }
    return 1;
}

int free_scaling_bloom(scaling_bloom_t *bloom)
{
    int i;
    for (i = bloom->num_blooms - 1; i >= 0; i--) {
        free_counting_bloom(*(bloom->blooms + i));
    }
    free(bloom->blooms);
    free(bloom->header);
    free_bitmap(bloom->bitmap);
    free(bloom);
    return 0;
}

/* creates a new counting bloom filter from a given scaling bloom filter, with count and id */
counting_bloom_t *new_counting_bloom_from_scale(scaling_bloom_t *bloom, uint32_t id, unsigned int count)
{
    int i, offset;
    double error_rate;
    counting_bloom_t *cur_bloom;
    
    error_rate = bloom->error_rate * (pow(.9, bloom->num_blooms + 1));
    
    if ((bloom->blooms = realloc(bloom->blooms, (bloom->num_blooms + 1) * sizeof(counting_bloom_t *))) == NULL) {
        fprintf(stderr, "Error, could not realloc a new bloom filter\n");
        return NULL;
    }
    
    cur_bloom = counting_bloom_init(bloom->capacity, error_rate, bloom->num_bytes, id, 0);
    bloom->blooms[bloom->num_blooms] = cur_bloom;
    
    bloom->bitmap = bitmap_resize(bloom->bitmap, bloom->num_bytes, bloom->num_bytes + cur_bloom->num_bytes);
    
    /* Set these values, as mmap may have moved */
    bloom->header->preseq = (uint64_t *)(bloom->bitmap->array);
    bloom->header->posseq = (uint64_t *)(bloom->bitmap->array + sizeof(uint64_t));
    bloom->header->max_id = (uint64_t *)(bloom->bitmap->array + 2 * sizeof(uint64_t));
    
    /* Set the pointers for these header structs to the right location since mmap may have moved */
    bloom->num_blooms++;
    for (i = 0; i < bloom->num_blooms; i++) {
        offset = bloom->blooms[i]->offset - HEADER_BYTES;
        bloom->blooms[i]->header->id    = (uint32_t *)(bloom->bitmap->array + offset);
        bloom->blooms[i]->header->count = (uint32_t *)(bloom->bitmap->array + offset + sizeof(uint32_t));
    }
    
    /* set the value for the current pointers */
    *cur_bloom->header->count = count;
    *cur_bloom->header->id = id;
    
    bloom->num_bytes += cur_bloom->num_bytes;
    cur_bloom->parent_bitmap = bloom->bitmap;
    
    return cur_bloom;
}


int scaling_bloom_add(scaling_bloom_t *bloom, const char *s, size_t len, uint32_t id)
{
    int i;
    int nblooms = bloom->num_blooms;
    counting_bloom_t *cur_bloom;
    for (i = nblooms - 1; i >= 0; i--) {
        cur_bloom = bloom->blooms[i];
        if (id >= *cur_bloom->header->id) {
            break;
        }
    }
    (*bloom->header->preseq) ++;
    
    if ((id > *bloom->header->max_id) && ((*(cur_bloom->header->count)) >= cur_bloom->capacity - 1)) {
        cur_bloom = new_counting_bloom_from_scale(bloom, (*bloom->header->max_id) + 1, 0);
    }
    if ((*bloom->header->max_id) < id) {
        (*bloom->header->max_id) = id;
    }
    counting_bloom_add(cur_bloom, s, len);
    
    (*bloom->header->posseq) ++;
    
    return 1;
}

int scaling_bloom_remove(scaling_bloom_t *bloom, const char *s, size_t len, uint32_t id)
{
    counting_bloom_t *cur_bloom;
    int id_diff, i;
    
    for (i = bloom->num_blooms - 1; i >= 0; i--) {
        cur_bloom = bloom->blooms[i];
        id_diff = id - (*cur_bloom->header->id);
        if (id_diff >= 0) {
            (*bloom->header->preseq)++;
            counting_bloom_remove(cur_bloom, s, len);
            (*bloom->header->posseq)++;
            return 1;
        }
    }
    return 0;
}

int scaling_bloom_check(scaling_bloom_t *bloom, const char *s, size_t len)
{
    int i;
    counting_bloom_t *cur_bloom;
    for (i = bloom->num_blooms - 1; i >= 0; i--) {
        cur_bloom = bloom->blooms[i];
        if (counting_bloom_check(cur_bloom, s, len)) {
            return 1;
        }
    }
    return 0;
}

int scaling_bloom_flush(scaling_bloom_t *bloom)
{
    return bitmap_flush(bloom->bitmap);
}

scaling_bloom_t *scaling_bloom_init(unsigned int capacity, double error_rate, const char *filename, int fd)
{
    scaling_bloom_t *bloom;
    
    if ((bloom = malloc(sizeof(scaling_bloom_t))) == NULL) {
        return NULL;
    }
    if ((bloom->header = malloc(sizeof(scaling_bloom_header_t))) == NULL) {
        fprintf(stderr, "Error, Maoolc for scaling bloom  header failed\n");
        return NULL;
    }
    if ((bloom->bitmap = new_bitmap(fd, SCALE_HEADER_BYTES)) == NULL) {
        fprintf(stderr, "Error, Could not create bitmap with file\n");
        free_scaling_bloom(bloom);
        return NULL;
    }
    
    bloom->capacity = capacity;
    bloom->error_rate = error_rate;
    bloom->num_blooms = 0;
    bloom->num_bytes = SCALE_HEADER_BYTES;
    bloom->fd = fd;
    bloom->blooms = NULL;
    
    return bloom;
}

scaling_bloom_t *new_scaling_bloom(unsigned int capacity, double error_rate, const char *filename, uint32_t id)
{

    scaling_bloom_t *bloom;
    counting_bloom_t *cur_bloom;
    int fd;
    
    if ((fd = open(filename, O_RDWR | O_CREAT | O_TRUNC, (mode_t)0600)) < 0) {
        perror("Error, Opening File Failed");
        fprintf(stderr, " %s \n", filename);
        return NULL;
    }
    
    bloom = scaling_bloom_init(capacity, error_rate, filename, fd);
    
    if (!(cur_bloom = new_counting_bloom_from_scale(bloom, id, 0))) {
        fprintf(stderr, "Error, Could not create counting bloom\n");
        free_scaling_bloom(bloom);
        return NULL;
    }
    
    return bloom;
}

scaling_bloom_t *new_scaling_bloom_from_file(unsigned int capacity, double error_rate, const char *filename)
{
    int fd;
    off_t size;
    uint32_t id;
    unsigned int count, offset;
    
    scaling_bloom_t *bloom;
    counting_bloom_t *cur_bloom;
    
    if ((fd = open(filename, O_RDWR, (mode_t)0600)) < 0) {
        fprintf(stderr, "Error, Could not open file %s with open: \n", filename);
        perror("");
        return NULL;
    }
    if ((size = lseek(fd, 0, SEEK_END)) < 0) {
        perror("Error, calling lseek() to tell file size");
        close(fd);
        return NULL;
    }
    if (size == 0) {
        fprintf(stderr, "Error, File size zero\n");
    }
    
    bloom = scaling_bloom_init(capacity, error_rate, filename, fd);
    
    bloom->header->preseq = (uint64_t *)(bloom->bitmap->array);
    bloom->header->posseq = (uint64_t *)(bloom->bitmap->array + sizeof(uint64_t));
    bloom->header->max_id = (uint64_t *)(bloom->bitmap->array + 2 * sizeof(uint64_t));
    
    offset = SCALE_HEADER_BYTES;
    size -= offset;
    while (size) {
        id    = *(uint32_t *)(bloom->bitmap->array + offset);
        count = *(uint32_t *)(bloom->bitmap->array + offset + sizeof(uint32_t));
        cur_bloom = new_counting_bloom_from_scale(bloom, id, count);
        size -= cur_bloom->num_bytes;
        offset += cur_bloom->num_bytes;
        if (size < 0) {
            free_scaling_bloom(bloom);
            fprintf(stderr, "Error, Actual filesize and expected filesize are not equal\n");
            return NULL;
        }
    }
    return bloom;
}
