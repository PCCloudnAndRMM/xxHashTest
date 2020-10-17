/*
 * xxhsum - Command line interface for xxhash algorithms
 * Copyright (C) 2013-2020 Yann Collet
 *
 * GPL v2 License
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * You can contact the author at:
 *   - xxHash homepage: https://www.xxhash.com
 *   - xxHash source repository: https://github.com/Cyan4973/xxHash
 */

/*
 * xxhsum:
 * Provides hash value of a file content, or a list of files, or stdin
 * Display convention is Big Endian, for both 32 and 64 bits algorithms
 */

/* Transitional headers */
#include "xsum_config.h"
#include "xsum_arch.h"
#include "xsum_os_specific.h"
#include "xsum_output.h"
#include "xsum_sanity_check.h"
#ifdef XXH_INLINE_ALL
#  include "xsum_os_specific.c"
#  include "xsum_output.c"
#  include "xsum_sanity_check.c"
#endif

/* ************************************
 *  Includes
 **************************************/
#include <limits.h>
#include <stdlib.h>     /* malloc, calloc, free, exit */
#include <string.h>     /* strcmp, memcpy */
#include <stdio.h>      /* fprintf, fopen, ftello64, fread, stdin, stdout, _fileno (when present) */
#include <sys/types.h>  /* stat, stat64, _stat64 */
#include <sys/stat.h>   /* stat, stat64, _stat64 */
#include <time.h>       /* clock_t, clock, CLOCKS_PER_SEC */
#include <assert.h>     /* assert */
#include <errno.h>      /* errno */
#include <dirent.h>

#define XXH_STATIC_LINKING_ONLY   /* *_state_t */
#include "xxhash.h"

#ifdef XXHSUM_DISPATCH
#  include "xxh_x86dispatch.h"
#endif

static unsigned XSUM_isLittleEndian(void)
{
    const union { XSUM_U32 u; XSUM_U8 c[4]; } one = { 1 };   /* don't use static: performance detrimental  */
    return one.c[0];
}

static const int g_nbBits = (int)(sizeof(void*)*8);
static const char g_lename[] = "little endian";
static const char g_bename[] = "big endian";
#define ENDIAN_NAME (XSUM_isLittleEndian() ? g_lename : g_bename)
static const char author[] = "Yann Collet";
#define WELCOME_MESSAGE(exename) "%s %s by %s \n", exename, XSUM_PROGRAM_VERSION, author
#define FULL_WELCOME_MESSAGE(exename) "%s %s by %s \n" \
                    "compiled as %i-bit %s %s with " XSUM_CC_VERSION_FMT " \n", \
                    exename, XSUM_PROGRAM_VERSION, author, \
                    g_nbBits, XSUM_ARCH, ENDIAN_NAME, XSUM_CC_VERSION

#define KB *( 1<<10)
#define MB *( 1<<20)
#define GB *(1U<<30)

static size_t XSUM_DEFAULT_SAMPLE_SIZE = 100 KB;
#define NBLOOPS    3                              /* Default number of benchmark iterations */
#define TIMELOOP_S 1
#define TIMELOOP  (TIMELOOP_S * CLOCKS_PER_SEC)   /* target timing per iteration */
#define TIMELOOP_MIN (TIMELOOP / 2)               /* minimum timing to validate a result */
#define XXHSUM32_DEFAULT_SEED 0                   /* Default seed for algo_xxh32 */
#define XXHSUM64_DEFAULT_SEED 0                   /* Default seed for algo_xxh64 */

#define MAX_MEM    (2 GB - 64 MB)

static const char stdinName[] = "-";
typedef enum { algo_xxh32=0, algo_xxh64=1, algo_xxh128=2 } AlgoSelected;
static AlgoSelected g_defaultAlgo = algo_xxh64;    /* required within main() & XSUM_usage() */

/* <16 hex char> <SPC> <SPC> <filename> <'\0'>
 * '4096' is typical Linux PATH_MAX configuration. */
#define DEFAULT_LINE_LENGTH (sizeof(XXH64_hash_t) * 2 + 2 + 4096 + 1)

/* Maximum acceptable line length. */
#define MAX_LINE_LENGTH (32 KB)


/* ************************************
 *  Display macros
 **************************************/


/* ************************************
 *  Local variables
 **************************************/
static XSUM_U32 g_nbIterations = NBLOOPS;


/* ************************************
 *  Benchmark Functions
 **************************************/
static clock_t XSUM_clockSpan( clock_t start )
{
    return clock() - start;   /* works even if overflow; Typical max span ~ 30 mn */
}

static size_t XSUM_findMaxMem(XSUM_U64 requiredMem)
{
    size_t const step = 64 MB;
    void* testmem = NULL;

    requiredMem = (((requiredMem >> 26) + 1) << 26);
    requiredMem += 2*step;
    if (requiredMem > MAX_MEM) requiredMem = MAX_MEM;

    while (!testmem) {
        if (requiredMem > step) requiredMem -= step;
        else requiredMem >>= 1;
        testmem = malloc ((size_t)requiredMem);
    }
    free (testmem);

    /* keep some space available */
    if (requiredMem > step) requiredMem -= step;
    else requiredMem >>= 1;

    return (size_t)requiredMem;
}

/*
 * Allocates a string containing s1 and s2 concatenated. Acts like strdup.
 * The result must be freed.
 */
static char* XSUM_strcatDup(const char* s1, const char* s2)
{
    assert(s1 != NULL);
    assert(s2 != NULL);
    {   size_t len1 = strlen(s1);
        size_t len2 = strlen(s2);
        char* buf = (char*)malloc(len1 + len2 + 1);
        if (buf != NULL) {
            /* strcpy(buf, s1) */
            memcpy(buf, s1, len1);
            /* strcat(buf, s2) */
            memcpy(buf + len1, s2, len2 + 1);
        }
        return buf;
    }
}


/*
 * A secret buffer used for benchmarking XXH3's withSecret variants.
 *
 * In order for the bench to be realistic, the secret buffer would need to be
 * pre-generated.
 *
 * Adding a pointer to the parameter list would be messy.
 */
static XSUM_U8 g_benchSecretBuf[XXH3_SECRET_SIZE_MIN];

/*
 * Wrappers for the benchmark.
 *
 * If you would like to add other hashes to the bench, create a wrapper and add
 * it to the g_hashesToBench table. It will automatically be added.
 */
typedef XSUM_U32 (*hashFunction)(const void* buffer, size_t bufferSize, XSUM_U32 seed);

static XSUM_U32 localXXH32(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    return XXH32(buffer, bufferSize, seed);
}
static XSUM_U32 localXXH64(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    return (XSUM_U32)XXH64(buffer, bufferSize, seed);
}
static XSUM_U32 localXXH3_64b(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    (void)seed;
    return (XSUM_U32)XXH3_64bits(buffer, bufferSize);
}
static XSUM_U32 localXXH3_64b_seeded(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    return (XSUM_U32)XXH3_64bits_withSeed(buffer, bufferSize, seed);
}
static XSUM_U32 localXXH3_64b_secret(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    (void)seed;
    return (XSUM_U32)XXH3_64bits_withSecret(buffer, bufferSize, g_benchSecretBuf, sizeof(g_benchSecretBuf));
}
static XSUM_U32 localXXH3_128b(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    (void)seed;
    return (XSUM_U32)(XXH3_128bits(buffer, bufferSize).low64);
}
static XSUM_U32 localXXH3_128b_seeded(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    return (XSUM_U32)(XXH3_128bits_withSeed(buffer, bufferSize, seed).low64);
}
static XSUM_U32 localXXH3_128b_secret(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    (void)seed;
    return (XSUM_U32)(XXH3_128bits_withSecret(buffer, bufferSize, g_benchSecretBuf, sizeof(g_benchSecretBuf)).low64);
}
static XSUM_U32 localXXH3_stream(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    XXH3_state_t state;
    (void)seed;
    XXH3_64bits_reset(&state);
    XXH3_64bits_update(&state, buffer, bufferSize);
    return (XSUM_U32)XXH3_64bits_digest(&state);
}
static XSUM_U32 localXXH3_stream_seeded(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    XXH3_state_t state;
    XXH3_INITSTATE(&state);
    XXH3_64bits_reset_withSeed(&state, (XXH64_hash_t)seed);
    XXH3_64bits_update(&state, buffer, bufferSize);
    return (XSUM_U32)XXH3_64bits_digest(&state);
}
static XSUM_U32 localXXH128_stream(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    XXH3_state_t state;
    (void)seed;
    XXH3_128bits_reset(&state);
    XXH3_128bits_update(&state, buffer, bufferSize);
    return (XSUM_U32)(XXH3_128bits_digest(&state).low64);
}
static XSUM_U32 localXXH128_stream_seeded(const void* buffer, size_t bufferSize, XSUM_U32 seed)
{
    XXH3_state_t state;
    XXH3_INITSTATE(&state);
    XXH3_128bits_reset_withSeed(&state, (XXH64_hash_t)seed);
    XXH3_128bits_update(&state, buffer, bufferSize);
    return (XSUM_U32)(XXH3_128bits_digest(&state).low64);
}


typedef struct {
    const char*  name;
    hashFunction func;
} hashInfo;

#define NB_HASHFUNC 12
static const hashInfo g_hashesToBench[NB_HASHFUNC] = {
    { "XXH32",             &localXXH32 },
    { "XXH64",             &localXXH64 },
    { "XXH3_64b",          &localXXH3_64b },
    { "XXH3_64b w/seed",   &localXXH3_64b_seeded },
    { "XXH3_64b w/secret", &localXXH3_64b_secret },
    { "XXH128",            &localXXH3_128b },
    { "XXH128 w/seed",     &localXXH3_128b_seeded },
    { "XXH128 w/secret",   &localXXH3_128b_secret },
    { "XXH3_stream",       &localXXH3_stream },
    { "XXH3_stream w/seed",&localXXH3_stream_seeded },
    { "XXH128_stream",     &localXXH128_stream },
    { "XXH128_stream w/seed",&localXXH128_stream_seeded },
};

#define NB_TESTFUNC (1 + 2 * NB_HASHFUNC)
static char g_testIDs[NB_TESTFUNC] = { 0 };
static const char k_testIDs_default[NB_TESTFUNC] = { 0,
        1 /*XXH32*/, 0,
        1 /*XXH64*/, 0,
        1 /*XXH3*/, 0, 0, 0, 0, 0,
        1 /*XXH128*/ };

#define HASHNAME_MAX 29
static void XSUM_benchHash(hashFunction h, const char* hName, int testID,
                          const void* buffer, size_t bufferSize)
{
    XSUM_U32 nbh_perIteration = (XSUM_U32)((300 MB) / (bufferSize+1)) + 1;  /* first iteration conservatively aims for 300 MB/s */
    unsigned iterationNb, nbIterations = g_nbIterations + !g_nbIterations /* min 1 */;
    double fastestH = 100000000.;
    assert(HASHNAME_MAX > 2);
    XSUM_logVerbose(2, "\r%80s\r", "");       /* Clean display line */

    for (iterationNb = 1; iterationNb <= nbIterations; iterationNb++) {
        XSUM_U32 r=0;
        clock_t cStart;

        XSUM_logVerbose(2, "%2u-%-*.*s : %10u ->\r",
                        iterationNb,
                        HASHNAME_MAX, HASHNAME_MAX, hName,
                        (unsigned)bufferSize);
        cStart = clock();
        while (clock() == cStart);   /* starts clock() at its exact beginning */
        cStart = clock();

        {   XSUM_U32 u;
            for (u=0; u<nbh_perIteration; u++)
                r += h(buffer, bufferSize, u);
        }
        if (r==0) XSUM_logVerbose(3,".\r");  /* do something with r to defeat compiler "optimizing" hash away */

        {   clock_t const nbTicks = XSUM_clockSpan(cStart);
            double const ticksPerHash = ((double)nbTicks / TIMELOOP) / nbh_perIteration;
            /*
             * clock() is the only decent portable timer, but it isn't very
             * precise.
             *
             * Sometimes, this lack of precision is enough that the benchmark
             * finishes before there are enough ticks to get a meaningful result.
             *
             * For example, on a Core 2 Duo (without any sort of Turbo Boost),
             * the imprecise timer caused peculiar results like so:
             *
             *    XXH3_64b                   4800.0 MB/s // conveniently even
             *    XXH3_64b unaligned         4800.0 MB/s
             *    XXH3_64b seeded            9600.0 MB/s // magical 2x speedup?!
             *    XXH3_64b seeded unaligned  4800.0 MB/s
             *
             * If we sense a suspiciously low number of ticks, we increase the
             * iterations until we can get something meaningful.
             */
            if (nbTicks < TIMELOOP_MIN) {
                /* Not enough time spent in benchmarking, risk of rounding bias */
                if (nbTicks == 0) { /* faster than resolution timer */
                    nbh_perIteration *= 100;
                } else {
                    /*
                     * update nbh_perIteration so that the next round lasts
                     * approximately 1 second.
                     */
                    double nbh_perSecond = (1 / ticksPerHash) + 1;
                    if (nbh_perSecond > (double)(4000U<<20)) nbh_perSecond = (double)(4000U<<20);   /* avoid overflow */
                    nbh_perIteration = (XSUM_U32)nbh_perSecond;
                }
                /* g_nbIterations==0 => quick evaluation, no claim of accuracy */
                if (g_nbIterations>0) {
                    iterationNb--;   /* new round for a more accurate speed evaluation */
                    continue;
                }
            }
            if (ticksPerHash < fastestH) fastestH = ticksPerHash;
            if (fastestH>0.) { /* avoid div by zero */
                XSUM_logVerbose(2, "%2u-%-*.*s : %10u -> %8.0f it/s (%7.1f MB/s) \r",
                            iterationNb,
                            HASHNAME_MAX, HASHNAME_MAX, hName,
                            (unsigned)bufferSize,
                            (double)1 / fastestH,
                            ((double)bufferSize / (1 MB)) / fastestH);
        }   }
        {   double nbh_perSecond = (1 / fastestH) + 1;
            if (nbh_perSecond > (double)(4000U<<20)) nbh_perSecond = (double)(4000U<<20);   /* avoid overflow */
            nbh_perIteration = (XSUM_U32)nbh_perSecond;
        }
    }
    XSUM_logVerbose(1, "%2i#%-*.*s : %10u -> %8.0f it/s (%7.1f MB/s) \n",
                    testID,
                    HASHNAME_MAX, HASHNAME_MAX, hName,
                    (unsigned)bufferSize,
                    (double)1 / fastestH,
                    ((double)bufferSize / (1 MB)) / fastestH);
    if (XSUM_logLevel<1)
        XSUM_logVerbose(0, "%u, ", (unsigned)((double)1 / fastestH));
}


/*!
 * XSUM_benchMem():
 * buffer: Must be 16-byte aligned.
 * The real allocated size of buffer is supposed to be >= (bufferSize+3).
 * returns: 0 on success, 1 if error (invalid mode selected)
 */
static void XSUM_benchMem(const void* buffer, size_t bufferSize)
{
    assert((((size_t)buffer) & 15) == 0);  /* ensure alignment */
    XSUM_fillTestBuffer(g_benchSecretBuf, sizeof(g_benchSecretBuf));
    {   int i;
        for (i = 1; i < NB_TESTFUNC; i++) {
            int const hashFuncID = (i-1) / 2;
            assert(g_hashesToBench[hashFuncID].name != NULL);
            if (g_testIDs[i] == 0) continue;
            /* aligned */
            if ((i % 2) == 1) {
                XSUM_benchHash(g_hashesToBench[hashFuncID].func, g_hashesToBench[hashFuncID].name, i, buffer, bufferSize);
            }
            /* unaligned */
            if ((i % 2) == 0) {
                /* Append "unaligned". */
                char* const hashNameBuf = XSUM_strcatDup(g_hashesToBench[hashFuncID].name, " unaligned");
                assert(hashNameBuf != NULL);
                XSUM_benchHash(g_hashesToBench[hashFuncID].func, hashNameBuf, i, ((const char*)buffer)+3, bufferSize);
                free(hashNameBuf);
            }
    }   }
}

static size_t XSUM_selectBenchedSize(const char* fileName)
{
    XSUM_U64 const inFileSize = XSUM_getFileSize(fileName);
    size_t benchedSize = (size_t) XSUM_findMaxMem(inFileSize);
    if ((XSUM_U64)benchedSize > inFileSize) benchedSize = (size_t)inFileSize;
    if (benchedSize < inFileSize) {
        XSUM_log("Not enough memory for '%s' full size; testing %i MB only...\n", fileName, (int)(benchedSize>>20));
    }
    return benchedSize;
}


static int XSUM_benchFiles(char*const* fileNamesTable, int nbFiles)
{
    int fileIdx;
    for (fileIdx=0; fileIdx<nbFiles; fileIdx++) {
        const char* const inFileName = fileNamesTable[fileIdx];
        assert(inFileName != NULL);

        {   FILE* const inFile = XSUM_fopen( inFileName, "rb" );
            size_t const benchedSize = XSUM_selectBenchedSize(inFileName);
            char* const buffer = (char*)calloc(benchedSize+16+3, 1);
            void* const alignedBuffer = (buffer+15) - (((size_t)(buffer+15)) & 0xF);  /* align on next 16 bytes */

            /* Checks */
            if (inFile==NULL){
                XSUM_log("Error: Could not open '%s': %s.\n", inFileName, strerror(errno));
                free(buffer);
                exit(11);
            }
            if(!buffer) {
                XSUM_log("\nError: Out of memory.\n");
                fclose(inFile);
                exit(12);
            }

            /* Fill input buffer */
            {   size_t const readSize = fread(alignedBuffer, 1, benchedSize, inFile);
                fclose(inFile);
                if(readSize != benchedSize) {
                    XSUM_log("\nError: Could not read '%s': %s.\n", inFileName, strerror(errno));
                    free(buffer);
                    exit(13);
            }   }

            /* bench */
            XSUM_benchMem(alignedBuffer, benchedSize);

            free(buffer);
    }   }
    return 0;
}


static int XSUM_benchInternal(size_t keySize)
{
    void* const buffer = calloc(keySize+16+3, 1);
    if (buffer == NULL) {
        XSUM_log("\nError: Out of memory.\n");
        exit(12);
    }

    {   const void* const alignedBuffer = ((char*)buffer+15) - (((size_t)((char*)buffer+15)) & 0xF);  /* align on next 16 bytes */

        /* bench */
        XSUM_logVerbose(1, "Sample of ");
        if (keySize > 10 KB) {
            XSUM_logVerbose(1, "%u KB", (unsigned)(keySize >> 10));
        } else {
            XSUM_logVerbose(1, "%u bytes", (unsigned)keySize);
        }
        XSUM_logVerbose(1, "...        \n");

        XSUM_benchMem(alignedBuffer, keySize);
        free(buffer);
    }
    return 0;
}

/* ********************************************************
*  File Hashing
**********************************************************/

/* for support of --little-endian display mode */
static void XSUM_display_LittleEndian(const void* ptr, size_t length)
{
    const XSUM_U8* const p = (const XSUM_U8*)ptr;
    size_t idx;
    for (idx=length-1; idx<length; idx--)    /* intentional underflow to negative to detect end */
        XSUM_output("%02x", p[idx]);
}

static void XSUM_display_BigEndian(const void* ptr, size_t length)
{
    const XSUM_U8* const p = (const XSUM_U8*)ptr;
    size_t idx;
    for (idx=0; idx<length; idx++)
        XSUM_output("%02x", p[idx]);
}

typedef union {
    XXH32_hash_t   xxh32;
    XXH64_hash_t   xxh64;
    XXH128_hash_t xxh128;
} Multihash;

/*
 * XSUM_hashStream:
 * Reads data from `inFile`, generating an incremental hash of type hashType,
 * using `buffer` of size `blockSize` for temporary storage.
 */
static int XSUM_hashStream(void* buffer, void* buffer2, size_t blockSize, double* timeTaken, size_t size)
{
    XXH3_state_t state128;
    (void)XXH3_128bits_reset(&state128);

    /* Load file & update hash */
    {
       
        clock_t t;
        t = clock();
        (void)XXH3_128bits_update(&state128, buffer, size);

        XXH128_hash_t finalHash = XXH3_128bits_digest(&state128);
    	
        t = clock() - t;

        *timeTaken = ((double)t);
    	
        XXH3_state_t state1281;
        (void)XXH3_128bits_reset(&state1281);
        (void)XXH3_128bits_update(&state1281, buffer2, size);

        XXH128_hash_t finalHash2 = XXH3_128bits_digest(&state1281);

        if (finalHash.high64 == finalHash2.high64 && finalHash.low64 == finalHash2.low64)
            return 1;
        return 0;
    }
}

static int XSUM_MemCmp(void* buffer, void* buffer2, size_t blockSize, double* timeTaken, size_t size)
{
        clock_t t;
        t = clock();
        const int result = memcmp(buffer, buffer2, size);
        t = clock() - t;

        *timeTaken = ((double)t);
        if (result == 0) return 1;
        return  0;
}
                                       /* algo_xxh32, algo_xxh64, algo_xxh128 */
static const char* XSUM_algoName[] =    { "XXH32",    "XXH64",    "XXH128" };
static const char* XSUM_algoLE_name[] = { "XXH32_LE", "XXH64_LE", "XXH128_LE" };
static const size_t XSUM_algoLength[] = { 4,          8,          16 };

#define XSUM_TABLE_ELT_SIZE(table)   (sizeof(table) / sizeof(*table))

typedef void (*XSUM_displayHash_f)(const void*, size_t);  /* display function signature */

static void XSUM_printLine_BSD_internal(const char* filename,
                                        const void* canonicalHash, const AlgoSelected hashType,
                                        const char* algoString[],
                                        XSUM_displayHash_f f_displayHash)
{
    assert(0 <= hashType && hashType <= XSUM_TABLE_ELT_SIZE(XSUM_algoName));
    {   const char* const typeString = algoString[hashType];
        const size_t hashLength = XSUM_algoLength[hashType];
        XSUM_output("%s (%s) = ", typeString, filename);
        f_displayHash(canonicalHash, hashLength);
        XSUM_output("\n");
}   }

static void XSUM_printLine_BSD_LE(const char* filename, const void* canonicalHash, const AlgoSelected hashType)
{
    XSUM_printLine_BSD_internal(filename, canonicalHash, hashType, XSUM_algoLE_name, XSUM_display_LittleEndian);
}

static void XSUM_printLine_BSD(const char* filename, const void* canonicalHash, const AlgoSelected hashType)
{
    XSUM_printLine_BSD_internal(filename, canonicalHash, hashType, XSUM_algoName, XSUM_display_BigEndian);
}

static void XSUM_printLine_GNU_internal(const char* filename,
                               const void* canonicalHash, const AlgoSelected hashType,
                               XSUM_displayHash_f f_displayHash)
{
    assert(0 <= hashType && hashType <= XSUM_TABLE_ELT_SIZE(XSUM_algoName));
    {   const size_t hashLength = XSUM_algoLength[hashType];
        f_displayHash(canonicalHash, hashLength);
        XSUM_output("  %s\n", filename);
}   }

static void XSUM_printLine_GNU(const char* filename,
                               const void* canonicalHash, const AlgoSelected hashType)
{
    XSUM_printLine_GNU_internal(filename, canonicalHash, hashType, XSUM_display_BigEndian);
}

static void XSUM_printLine_GNU_LE(const char* filename,
                                  const void* canonicalHash, const AlgoSelected hashType)
{
    XSUM_printLine_GNU_internal(filename, canonicalHash, hashType, XSUM_display_LittleEndian);
}

typedef enum { big_endian, little_endian} Display_endianess;

typedef enum { display_gnu, display_bsd } Display_convention;

typedef void (*XSUM_displayLine_f)(const char*, const void*, AlgoSelected);  /* line display signature */

static XSUM_displayLine_f XSUM_kDisplayLine_fTable[2][2] = {
    { XSUM_printLine_GNU, XSUM_printLine_GNU_LE },
    { XSUM_printLine_BSD, XSUM_printLine_BSD_LE }
};

static int XSUM_hashFile( )
{
    char* in_dir="/opt/test/";
    
    size_t const blockSize = 10240 KB;

    FILE* inFile;
    FILE* inFile2;
    DIR* FD;
    struct dirent* in_file;
    struct dirent* in_file2;
    if (NULL == (FD = opendir(in_dir)))
    {
        fprintf(stderr, "Error : Failed to open input directory - %s\n", strerror(errno));
        return 1;
    }
    double TimeTakenForIteration = 0;
    int count = 0;
    char* filename1 = 0;
    size_t readSize = 0;
    void* buffer = 0;
    while ((in_file = readdir(FD)))
    {

        if (!strcmp(in_file->d_name, "."))
            continue;
        if (!strcmp(in_file->d_name, ".."))
            continue;
        if (!strcmp(in_file->d_name, ".DS_Store"))
            continue;
        filename1 = (char*)malloc(1 + strlen(in_file->d_name));
        strcpy(filename1, in_file->d_name);
        char* file_name = (char*)malloc(1 + strlen(in_dir) + strlen(in_file->d_name));
        strcpy(file_name, in_dir);
        strcat(file_name, in_file->d_name);
        inFile = fopen(file_name, "rb");
        buffer = malloc(blockSize);
        readSize = fread(buffer, 1, blockSize, inFile);
        fclose(inFile);
        break;
    }
    while ((in_file2 = readdir(FD)))
    {
        /* On linux/Unix we don't want current and parent directories
         * On windows machine too, thanks Greg Hewgill
         */
        if (!strcmp(in_file2->d_name, "."))
            continue;
        if (!strcmp(in_file2->d_name, ".."))
            continue;

        char* file_name2 = (char*)malloc(1 + strlen(in_dir) + strlen(in_file2->d_name));
        strcpy(file_name2, in_dir);
        strcat(file_name2, in_file2->d_name);



        inFile2 = fopen(file_name2, "rb");
        void* const buffer2 = malloc(blockSize);
        size_t readSize2 = fread(buffer2, 1, blockSize, inFile2);

        if (readSize2 != readSize)
        {
            continue;
        }

        double totalTimeTaken = 0;
        int result = 0;
        for (int i = 0; i <= 100; i++)
        {
            double timeTaken = 0;
            result = XSUM_hashStream(buffer, buffer2, blockSize, &timeTaken, readSize2);
            totalTimeTaken += timeTaken * 1000 / CLOCKS_PER_SEC;
        }


        fclose(inFile2);
        free(buffer2);

        TimeTakenForIteration += totalTimeTaken / 100;
        count++;
        printf("%-40s  %-40s  %-10s  %-10f\n", filename1, in_file2->d_name, result == 1 ? "duplicate" : "different", (totalTimeTaken / 100));
    }
    free(buffer);
    printf("Hash comparision completed, average time:%f\n", TimeTakenForIteration / count);
    return 0;
}

static int XSUM_MemCmpTest()
{
    char* in_dir="/opt/test/";
    size_t const blockSize = 10240 KB;

    FILE* inFile;
    FILE* inFile2;
    DIR* FD;
    struct dirent* in_file;
    struct dirent* in_file2;
    if (NULL == (FD = opendir(in_dir)))
    {
        fprintf(stderr, "Error : Failed to open input directory - %s\n", strerror(errno));
        return 1;
    }
    double TimeTakenForIteration = 0;
    int count = 0;
    char* filename1 = 0;
    size_t readSize = 0;
    void* buffer = 0;
    while ((in_file = readdir(FD)))
    {

        if (!strcmp(in_file->d_name, "."))
            continue;
        if (!strcmp(in_file->d_name, ".."))
            continue;
        if (!strcmp(in_file->d_name, ".DS_Store"))
            continue;
        filename1 = (char*)malloc(1 + strlen(in_file->d_name));
        strcpy(filename1, in_file->d_name);
        char* file_name = (char*)malloc(1 + strlen(in_dir) + strlen(in_file->d_name));
        strcpy(file_name, in_dir);
        strcat(file_name, in_file->d_name);
    	inFile = fopen(file_name, "rb");
        buffer = malloc(blockSize);
        readSize = fread(buffer, 1, blockSize, inFile);
        fclose(inFile);
        break;
    }
    while ((in_file2 = readdir(FD)))
    {
        /* On linux/Unix we don't want current and parent directories
         * On windows machine too, thanks Greg Hewgill
         */

        if (!strcmp(in_file2->d_name, "."))
            continue;
        if (!strcmp(in_file2->d_name, ".."))
            continue;

        char* file_name2 = (char*)malloc(1 + strlen(in_dir) + strlen(in_file2->d_name));
        strcpy(file_name2, in_dir);
        strcat(file_name2, in_file2->d_name);

       

        inFile2 = fopen(file_name2, "rb");
        void* const buffer2 = malloc(blockSize);
        size_t readSize2 = fread(buffer2, 1, blockSize, inFile2);

        if (readSize2 != readSize)
        {
            continue;
        }

        double totalTimeTaken = 0;
        int result = 0;
        for (int i = 0; i <= 100; i++)
        {
            double timeTaken = 0;
            result = XSUM_MemCmp(buffer, buffer2, blockSize, &timeTaken, readSize2);
            totalTimeTaken += timeTaken * 1000 / CLOCKS_PER_SEC;
        }
       
        
        fclose(inFile2);
        free(buffer2);

        TimeTakenForIteration += totalTimeTaken / 100;
        count++;
        printf("%-40s  %-40s  %-10s  %-10f\n", filename1, in_file2->d_name, result == 1 ? "duplicate" : "different", (totalTimeTaken / 100));
    }
	free(buffer);
    printf("Mem comparision completed, average time:%f\n", TimeTakenForIteration / count);

return 0;
}



typedef enum {
    GetLine_ok,
    GetLine_eof,
    GetLine_exceedMaxLineLength,
    GetLine_outOfMemory
} GetLineResult;

typedef enum {
    CanonicalFromString_ok,
    CanonicalFromString_invalidFormat
} CanonicalFromStringResult;

typedef enum {
    ParseLine_ok,
    ParseLine_invalidFormat
} ParseLineResult;

typedef enum {
    LineStatus_hashOk,
    LineStatus_hashFailed,
    LineStatus_failedToOpen
} LineStatus;

typedef union {
    XXH32_canonical_t xxh32;
    XXH64_canonical_t xxh64;
    XXH128_canonical_t xxh128;
} Canonical;

typedef struct {
    Canonical   canonical;
    const char* filename;
    int         xxhBits;    /* canonical type: 32:xxh32, 64:xxh64, 128:xxh128 */
} ParsedLine;

typedef struct {
    unsigned long   nProperlyFormattedLines;
    unsigned long   nImproperlyFormattedLines;
    unsigned long   nMismatchedChecksums;
    unsigned long   nOpenOrReadFailures;
    unsigned long   nMixedFormatLines;
    int             quit;
} ParseFileReport;

typedef struct {
    const char*     inFileName;
    FILE*           inFile;
    int             lineMax;
    char*           lineBuf;
    size_t          blockSize;
    char*           blockBuf;
    XSUM_U32             strictMode;
    XSUM_U32             statusOnly;
    XSUM_U32             warn;
    XSUM_U32             quiet;
    ParseFileReport report;
} ParseFileArg;


/*
 * Reads a line from stream `inFile`.
 * Returns GetLine_ok, if it reads line successfully.
 * Returns GetLine_eof, if stream reaches EOF.
 * Returns GetLine_exceedMaxLineLength, if line length is longer than MAX_LINE_LENGTH.
 * Returns GetLine_outOfMemory, if line buffer memory allocation failed.
 */
static GetLineResult XSUM_getLine(char** lineBuf, int* lineMax, FILE* inFile)
{
    GetLineResult result = GetLine_ok;
    size_t len = 0;

    if ((*lineBuf == NULL) || (*lineMax<1)) {
        free(*lineBuf);  /* in case it's != NULL */
        *lineMax = 0;
        *lineBuf = (char*)malloc(DEFAULT_LINE_LENGTH);
        if(*lineBuf == NULL) return GetLine_outOfMemory;
        *lineMax = DEFAULT_LINE_LENGTH;
    }

    for (;;) {
        const int c = fgetc(inFile);
        if (c == EOF) {
            /*
             * If we meet EOF before first character, returns GetLine_eof,
             * otherwise GetLine_ok.
             */
            if (len == 0) result = GetLine_eof;
            break;
        }

        /* Make enough space for len+1 (for final NUL) bytes. */
        if (len+1 >= (size_t)*lineMax) {
            char* newLineBuf = NULL;
            size_t newBufSize = (size_t)*lineMax;

            newBufSize += (newBufSize/2) + 1; /* x 1.5 */
            if (newBufSize > MAX_LINE_LENGTH) newBufSize = MAX_LINE_LENGTH;
            if (len+1 >= newBufSize) return GetLine_exceedMaxLineLength;

            newLineBuf = (char*) realloc(*lineBuf, newBufSize);
            if (newLineBuf == NULL) return GetLine_outOfMemory;

            *lineBuf = newLineBuf;
            *lineMax = (int)newBufSize;
        }

        if (c == '\n') break;
        (*lineBuf)[len++] = (char) c;
    }

    (*lineBuf)[len] = '\0';
    return result;
}


/*
 * Converts one hexadecimal character to integer.
 * Returns -1 if the given character is not hexadecimal.
 */
static int charToHex(char c)
{
    int result = -1;
    if (c >= '0' && c <= '9') {
        result = (int) (c - '0');
    } else if (c >= 'A' && c <= 'F') {
        result = (int) (c - 'A') + 0x0a;
    } else if (c >= 'a' && c <= 'f') {
        result = (int) (c - 'a') + 0x0a;
    }
    return result;
}


/*
 * Converts canonical ASCII hexadecimal string `hashStr`
 * to the big endian binary representation in unsigned char array `dst`.
 *
 * Returns CanonicalFromString_invalidFormat if hashStr is not well formatted.
 * Returns CanonicalFromString_ok if hashStr is parsed successfully.
 */
static CanonicalFromStringResult XSUM_canonicalFromString(unsigned char* dst,
                                                          size_t dstSize,
                                                          const char* hashStr,
                                                          int reverseBytes)
{
    size_t i;
    for (i = 0; i < dstSize; ++i) {
        int h0, h1;
        size_t j = reverseBytes ? dstSize - i - 1 : i;

        h0 = charToHex(hashStr[j*2 + 0]);
        if (h0 < 0) return CanonicalFromString_invalidFormat;

        h1 = charToHex(hashStr[j*2 + 1]);
        if (h1 < 0) return CanonicalFromString_invalidFormat;

        dst[i] = (unsigned char) ((h0 << 4) | h1);
    }
    return CanonicalFromString_ok;
}


/*
 * Parse single line of xxHash checksum file.
 * Returns ParseLine_invalidFormat if the line is not well formatted.
 * Returns ParseLine_ok if the line is parsed successfully.
 * And members of XSUM_parseLine will be filled by parsed values.
 *
 *  - line must be terminated with '\0' without a trailing newline.
 *  - Since parsedLine.filename will point within given argument `line`,
 *    users must keep `line`s content when they are using parsedLine.
 *  - The line may be modified to carve up the information it contains.
 *
 * xxHash checksum lines should have the following format:
 *
 *      <8, 16, or 32 hexadecimal char> <space> <space> <filename...> <'\0'>
 *
 * or:
 *
 *      <algorithm> <' ('> <filename> <') = '> <hexstring> <'\0'>
 */
static ParseLineResult XSUM_parseLine(ParsedLine* parsedLine, char* line, int rev)
{
    char* const firstSpace = strchr(line, ' ');
    const char* hash_ptr;
    size_t hash_len;

    parsedLine->filename = NULL;
    parsedLine->xxhBits = 0;

    if (firstSpace == NULL || !firstSpace[1]) return ParseLine_invalidFormat;

    if (firstSpace[1] == '(') {
        char* lastSpace = strrchr(line, ' ');
        if (lastSpace - firstSpace < 5) return ParseLine_invalidFormat;
        if (lastSpace[-1] != '=' || lastSpace[-2] != ' ' || lastSpace[-3] != ')') return ParseLine_invalidFormat;
        lastSpace[-3] = '\0'; /* Terminate the filename */
        *firstSpace = '\0';
        rev = strstr(line, "_LE") != NULL; /* was output little-endian */
        hash_ptr = lastSpace + 1;
        hash_len = strlen(hash_ptr);
        /* NOTE: This currently ignores the hash description at the start of the string.
         * In the future we should parse it and verify that it matches the hash length.
         * It could also be used to allow both XXH64 & XXH3_64bits to be differentiated. */
    } else {
        hash_ptr = line;
        hash_len = (size_t)(firstSpace - line);
    }

    switch (hash_len)
    {
    case 8:
        {   XXH32_canonical_t* xxh32c = &parsedLine->canonical.xxh32;
            if (XSUM_canonicalFromString(xxh32c->digest, sizeof(xxh32c->digest), hash_ptr, rev)
                != CanonicalFromString_ok) {
                return ParseLine_invalidFormat;
            }
            parsedLine->xxhBits = 32;
            break;
        }

    case 16:
        {   XXH64_canonical_t* xxh64c = &parsedLine->canonical.xxh64;
            if (XSUM_canonicalFromString(xxh64c->digest, sizeof(xxh64c->digest), hash_ptr, rev)
                != CanonicalFromString_ok) {
                return ParseLine_invalidFormat;
            }
            parsedLine->xxhBits = 64;
            break;
        }

    case 32:
        {   XXH128_canonical_t* xxh128c = &parsedLine->canonical.xxh128;
            if (XSUM_canonicalFromString(xxh128c->digest, sizeof(xxh128c->digest), hash_ptr, rev)
                != CanonicalFromString_ok) {
                return ParseLine_invalidFormat;
            }
            parsedLine->xxhBits = 128;
            break;
        }

    default:
            return ParseLine_invalidFormat;
            break;
    }

    /* note : skipping second separation character, which can be anything,
     * allowing insertion of custom markers such as '*' */
    parsedLine->filename = firstSpace + 2;
    return ParseLine_ok;
}


/* ********************************************************
*  Main
**********************************************************/

static int XSUM_usage(const char* exename)
{
    XSUM_log( WELCOME_MESSAGE(exename) );
    XSUM_log( "Print or verify checksums using fast non-cryptographic algorithm xxHash \n\n" );
    XSUM_log( "Usage: %s [options] [files] \n\n", exename);
    XSUM_log( "When no filename provided or when '-' is provided, uses stdin as input. \n");
    XSUM_log( "Options: \n");
    XSUM_log( "  -H#         algorithm selection: 0,1,2 or 32,64,128 (default: %i) \n", (int)g_defaultAlgo);
    XSUM_log( "  -c, --check read xxHash checksum from [files] and check them \n");
    XSUM_log( "  -h, --help  display a long help page about advanced options \n");
    return 0;
}


static int XSUM_usage_advanced(const char* exename)
{
    XSUM_usage(exename);
    XSUM_log( "Advanced :\n");
    XSUM_log( "  -V, --version        Display version information \n");
    XSUM_log( "      --tag            Produce BSD-style checksum lines \n");
    XSUM_log( "      --little-endian  Checksum values use little endian convention (default: big endian) \n");
    XSUM_log( "  -b                   Run benchmark \n");
    XSUM_log( "  -b#                  Bench only algorithm variant # \n");
    XSUM_log( "  -i#                  Number of times to run the benchmark (default: %u) \n", (unsigned)g_nbIterations);
    XSUM_log( "  -q, --quiet          Don't display version header in benchmark mode \n");
    XSUM_log( "\n");
    XSUM_log( "The following four options are useful only when verifying checksums (-c): \n");
    XSUM_log( "  -q, --quiet          Don't print OK for each successfully verified file \n");
    XSUM_log( "      --status         Don't output anything, status code shows success \n");
    XSUM_log( "      --strict         Exit non-zero for improperly formatted checksum lines \n");
    XSUM_log( "      --warn           Warn about improperly formatted checksum lines \n");
    return 0;
}

static int XSUM_badusage(const char* exename)
{
    XSUM_log("Wrong parameters\n\n");
    XSUM_usage(exename);
    return 1;
}

static void errorOut(const char* msg)
{
    XSUM_log("%s \n", msg);
    exit(1);
}

static const char* XSUM_lastNameFromPath(const char* path)
{
    const char* name = path;
    if (strrchr(name, '/')) name = strrchr(name, '/') + 1;
    if (strrchr(name, '\\')) name = strrchr(name, '\\') + 1; /* windows */
    return name;
}

/*!
 * XSUM_readU32FromCharChecked():
 * @return 0 if success, and store the result in *value.
 * Allows and interprets K, KB, KiB, M, MB and MiB suffix.
 * Will also modify `*stringPtr`, advancing it to position where it stopped reading.
 * @return 1 if an overflow error occurs
 */
static int XSUM_readU32FromCharChecked(const char** stringPtr, XSUM_U32* value)
{
    static const XSUM_U32 max = (((XSUM_U32)(-1)) / 10) - 1;
    XSUM_U32 result = 0;
    while ((**stringPtr >='0') && (**stringPtr <='9')) {
        if (result > max) return 1; /* overflow error */
        result *= 10;
        result += (XSUM_U32)(**stringPtr - '0');
        (*stringPtr)++ ;
    }
    if ((**stringPtr=='K') || (**stringPtr=='M')) {
        XSUM_U32 const maxK = ((XSUM_U32)(-1)) >> 10;
        if (result > maxK) return 1; /* overflow error */
        result <<= 10;
        if (**stringPtr=='M') {
            if (result > maxK) return 1; /* overflow error */
            result <<= 10;
        }
        (*stringPtr)++;  /* skip `K` or `M` */
        if (**stringPtr=='i') (*stringPtr)++;
        if (**stringPtr=='B') (*stringPtr)++;
    }
    *value = result;
    return 0;
}

/*!
 * XSUM_readU32FromChar():
 * @return: unsigned integer value read from input in `char` format.
 *  allows and interprets K, KB, KiB, M, MB and MiB suffix.
 *  Will also modify `*stringPtr`, advancing it to position where it stopped reading.
 *  Note: function will exit() program if digit sequence overflows
 */
static XSUM_U32 XSUM_readU32FromChar(const char** stringPtr) {
    XSUM_U32 result;
    if (XSUM_readU32FromCharChecked(stringPtr, &result)) {
        static const char errorMsg[] = "Error: numeric value too large";
        errorOut(errorMsg);
    }
    return result;
}

XSUM_API int XSUM_main(int argc, char* argv[])
{
    printf("----Comparison of Memcmp and xxHash-----\n");
    char* path = "/opt/test/";
    int iterationPerFile = 500;
    if (argc > 1)
        path = argv[1];
    if (argc > 2)
        iterationPerFile = atoi(argv[2]);
    printf("Starting with Path:%s with %d iterations per file\n", path, iterationPerFile);
    printf("Processing With xxHash\n");
    XSUM_hashFile();
    printf("----------------------------------------------------------------------------------\n");
    printf("Processing With MemComp\n");
    XSUM_MemCmpTest();
    return 0;
}
