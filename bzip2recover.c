/*-----------------------------------------------------------*/
/*--- Block recoverer program for bzip2                   ---*/
/*---                                      bzip2recover.c ---*/
/*-----------------------------------------------------------*/

/* ------------------------------------------------------------------
   This file is part of bzip2/libbzip2, a program and library for
   lossless, block-sorting data compression.

   bzip2/libbzip2 version 1.1.0 of 6 September 2010
   Copyright (C) 1996-2010 Julian Seward <jseward@acm.org>

   Please read the WARNING, DISCLAIMER and PATENTS sections in the
   README file.

   This program is released under the terms of the license contained
   in the file LICENSE.
   ------------------------------------------------------------------ */

/* This program is a complete hack and should be rewritten properly.
   It isn't very complicated. */

#if BZ_UNIX
#   include <fcntl.h>
#   include <sys/types.h>
#   include <sys/stat.h>
#   include <unistd.h>
#endif

#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>


/* This program records bit locations in the file to be recovered.
   That means that if 64-bit ints are not supported, we will not
   be able to recover .bz2 files over 512MB (2^32 bits) long.
   On GNU supported platforms, we take advantage of the 64-bit
   int support to circumvent this problem.  Ditto MSVC.

   This change occurred in version 1.0.2; all prior versions have
   the 512MB limitation.
*/

#define BZ_MAX_FILENAME 2000

char inFileName[BZ_MAX_FILENAME];
char outFileName[BZ_MAX_FILENAME];
char progName[BZ_MAX_FILENAME];

uint64_t bytesOut = UINT64_C(0);
uint64_t bytesIn  = UINT64_C(0);


/*---------------------------------------------------*/
/*--- Header bytes                                ---*/
/*---------------------------------------------------*/

#define BZ_HDR_B 0x42                         /* 'B' */
#define BZ_HDR_Z 0x5a                         /* 'Z' */
#define BZ_HDR_h 0x68                         /* 'h' */
#define BZ_HDR_0 0x30                         /* '0' */


/*---------------------------------------------------*/
/*--- I/O errors                                  ---*/
/*---------------------------------------------------*/

/*---------------------------------------------*/
static void readError ( void )
{
   fprintf ( stderr,
             "%s: I/O error reading `%s', possible reason follows.\n",
            progName, inFileName );
   perror ( progName );
   fprintf ( stderr, "%s: warning: output file(s) may be incomplete.\n",
             progName );
   exit ( 1 );
}


/*---------------------------------------------*/
static void writeError ( void )
{
   fprintf ( stderr,
             "%s: I/O error reading `%s', possible reason follows.\n",
            progName, inFileName );
   perror ( progName );
   fprintf ( stderr, "%s: warning: output file(s) may be incomplete.\n",
             progName );
   exit ( 1 );
}


/*---------------------------------------------*/
static void mallocFail ( int32_t n )
{
   fprintf ( stderr,
             "%s: malloc failed on request for %d bytes.\n",
            progName, n );
   fprintf ( stderr, "%s: warning: output file(s) may be incomplete.\n",
             progName );
   exit ( 1 );
}


/*---------------------------------------------*/
static void tooManyBlocks ( int32_t max_handled_blocks )
{
   fprintf ( stderr,
             "%s: `%s' appears to contain more than %d blocks\n",
            progName, inFileName, max_handled_blocks );
   fprintf ( stderr,
             "%s: and cannot be handled.  To fix, increase\n",
             progName );
   fprintf ( stderr,
             "%s: BZ_MAX_HANDLED_BLOCKS in bzip2recover.c, and recompile.\n",
             progName );
   exit ( 1 );
}



/*---------------------------------------------------*/
/*--- Bit stream I/O                              ---*/
/*---------------------------------------------------*/

typedef
   struct {
      FILE*    handle;
      int32_t  buffer;
      int32_t  buffLive;
      char     mode;
   }
   BitStream;


/*---------------------------------------------*/
static BitStream* bsOpenReadStream ( FILE* stream )
{
   BitStream *bs = malloc ( sizeof(BitStream) );
   if (bs == NULL) mallocFail ( sizeof(BitStream) );
   bs->handle = stream;
   bs->buffer = 0;
   bs->buffLive = 0;
   bs->mode = 'r';
   return bs;
}


/*---------------------------------------------*/
static BitStream* bsOpenWriteStream ( FILE* stream )
{
   BitStream *bs = malloc ( sizeof(BitStream) );
   if (bs == NULL) mallocFail ( sizeof(BitStream) );
   bs->handle = stream;
   bs->buffer = 0;
   bs->buffLive = 0;
   bs->mode = 'w';
   return bs;
}


/*---------------------------------------------*/
static void bsPutBit ( BitStream* bs, int32_t bit )
{
   if (bs->buffLive == 8) {
      int32_t retVal = putc ( bs->buffer, bs->handle );
      if (retVal == EOF) writeError();
      bytesOut++;
      bs->buffLive = 1;
      bs->buffer = bit & 0x1;
   } else {
      bs->buffer = ( (bs->buffer << 1) | (bit & 0x1) );
      bs->buffLive++;
   };
}


/*---------------------------------------------*/
/*--
   Returns 0 or 1, or 2 to indicate EOF.
--*/
static int32_t bsGetBit ( BitStream* bs )
{
   if (bs->buffLive > 0) {
      bs->buffLive --;
      return ( ((bs->buffer) >> (bs->buffLive)) & 0x1 );
   } else {
      int32_t retVal = getc ( bs->handle );
      if ( retVal == EOF ) {
         if (errno != 0) readError();
         return 2;
      }
      bs->buffLive = 7;
      bs->buffer = retVal;
      return ( ((bs->buffer) >> 7) & 0x1 );
   }
}


/*---------------------------------------------*/
static void bsClose ( BitStream* bs )
{
   int32_t retVal;

   if ( bs->mode == 'w' ) {
      while ( bs->buffLive < 8 ) {
         bs->buffLive++;
         bs->buffer <<= 1;
      };
      retVal = putc ( bs->buffer, bs->handle );
      if (retVal == EOF) writeError();
      bytesOut++;
      retVal = fflush ( bs->handle );
      if (retVal == EOF) writeError();
   }
   retVal = fclose ( bs->handle );
   if (retVal == EOF) {
      if (bs->mode == 'w') writeError(); else readError();
   }
   free ( bs );
}


/*---------------------------------------------*/
static void bsPutUChar ( BitStream* bs, uint8_t c )
{
   int32_t i;
   for (i = 7; i >= 0; i--)
      bsPutBit ( bs, (((uint32_t) c) >> i) & 0x1 );
}


/*---------------------------------------------*/
static void bsPutUInt32 ( BitStream* bs, uint32_t c )
{
   int32_t i;

   for (i = 31; i >= 0; i--)
      bsPutBit ( bs, (c >> i) & 0x1 );
}


/*---------------------------------------------*/
static bool endsInBz2 ( const char* name )
{
   int32_t n = strlen ( name );
   if (n <= 4) return false;
   return
      (name[n-4] == '.' &&
       name[n-3] == 'b' &&
       name[n-2] == 'z' &&
       name[n-1] == '2');
}

/* Same as from bzip2.c
 *
 * Opens a file, but refuses to overwrite an existing one.
 */
static
FILE* fopen_output_safely ( const char* name, const char* mode )
{
#  if BZ_UNIX
   FILE*     fp;
   int       fh;
   fh = open(name, O_WRONLY|O_CREAT|O_EXCL, S_IWUSR|S_IRUSR);
   if (fh == -1) return NULL;
   fp = fdopen(fh, mode);
   if (fp == NULL) close(fh);
   return fp;
#  else
   return fopen(name, mode);
#  endif
}



/*---------------------------------------------------*/
/*---                                             ---*/
/*---------------------------------------------------*/

/* This logic isn't really right when it comes to Cygwin. */
#ifdef _WIN32
#  define  BZ_SPLIT_SYM  '\\'  /* path splitter on Windows platform */
#else
#  define  BZ_SPLIT_SYM  '/'   /* path splitter on Unix platform */
#endif

#define BLOCK_HEADER_HI  0x00003141U
#define BLOCK_HEADER_LO  0x59265359U

#define BLOCK_ENDMARK_HI 0x00001772U
#define BLOCK_ENDMARK_LO 0x45385090U

/* Increase if necessary.  However, a .bz2 file with > 50000 blocks
   would have an uncompressed size of at least 40GB, so the chances
   are low you'll need to up this.
*/
#define BZ_MAX_HANDLED_BLOCKS 50000

uint64_t bStart [BZ_MAX_HANDLED_BLOCKS];
uint64_t bEnd   [BZ_MAX_HANDLED_BLOCKS];
uint64_t rbStart[BZ_MAX_HANDLED_BLOCKS];
uint64_t rbEnd  [BZ_MAX_HANDLED_BLOCKS];

int main ( int argc, char** argv )
{
   FILE*       inFile;
   FILE*       outFile;
   BitStream*  bsIn, *bsWr;
   int32_t     b, wrBlock, currBlock, rbCtr;
   uint64_t    bitsRead;

   uint32_t    buffHi, buffLo, blockCRC;
   char*       p;

   strncpy ( progName, argv[0], BZ_MAX_FILENAME-1);
   progName[BZ_MAX_FILENAME-1]='\0';
   inFileName[0] = outFileName[0] = 0;

   fprintf ( stderr,
             "bzip2recover 1.0.6: extracts blocks from damaged .bz2 files.\n" );

   if (argc != 2) {
      fprintf ( stderr, "%s: usage is `%s damaged_file_name'.\n",
                        progName, progName );
      fprintf ( stderr,
               "\trestrictions on size of recovered file: None\n" );
      exit(1);
   }

   if (strlen(argv[1]) >= BZ_MAX_FILENAME-20) {
      fprintf ( stderr,
                "%s: supplied filename is suspiciously (>= %d chars) long.  Bye!\n",
                progName, (int)strlen(argv[1]) );
      exit(1);
   }

   strcpy ( inFileName, argv[1] );

   inFile = fopen ( inFileName, "rb" );
   if (inFile == NULL) {
      fprintf ( stderr, "%s: can't read `%s'\n", progName, inFileName );
      exit(1);
   }

   bsIn = bsOpenReadStream ( inFile );
   fprintf ( stderr, "%s: searching for block boundaries ...\n", progName );

   bitsRead = UINT64_C(0);
   buffHi = buffLo = 0U;
   currBlock = 0;
   bStart[currBlock] = UINT64_C(0);

   rbCtr = 0;

   while (true) {
      b = bsGetBit ( bsIn );
      bitsRead++;
      if (b == 2) {
         if (bitsRead >= bStart[currBlock] &&
            (bitsRead - bStart[currBlock]) >= UINT64_C(40)) {
            bEnd[currBlock] = bitsRead - UINT64_C(1);
            if (currBlock > 0)
               fprintf ( stderr, "   block %d runs from %" PRIu64
                                 " to %" PRIu64 " (incomplete)\n",
                         currBlock,  bStart[currBlock], bEnd[currBlock] );
         } else
            currBlock--;
         break;
      }
      buffHi = (buffHi << 1) | (buffLo >> 31);
      buffLo = (buffLo << 1) | (b & 1);
      if ( ( (buffHi & 0xffffU) == BLOCK_HEADER_HI
             && buffLo == BLOCK_HEADER_LO)
           ||
           ( (buffHi & 0xffffU) == BLOCK_ENDMARK_HI
             && buffLo == BLOCK_ENDMARK_LO)
         ) {
         if (bitsRead > UINT64_C(49)) {
            bEnd[currBlock] = bitsRead - UINT64_C(49);
         } else {
            bEnd[currBlock] = UINT64_C(0);
         }
         if (currBlock > 0 &&
             (bEnd[currBlock] - bStart[currBlock]) >= UINT64_C(130)) {
            fprintf ( stderr, "   block %d runs from %" PRIu64
                              " to %" PRIu64 "\n",
                      rbCtr+1,  bStart[currBlock], bEnd[currBlock] );
            rbStart[rbCtr] = bStart[currBlock];
            rbEnd[rbCtr] = bEnd[currBlock];
            rbCtr++;
         }
         if (currBlock >= BZ_MAX_HANDLED_BLOCKS)
            tooManyBlocks(BZ_MAX_HANDLED_BLOCKS);
         currBlock++;

         bStart[currBlock] = bitsRead;
      }
   }

   bsClose ( bsIn );

   /*-- identified blocks run from 1 to rbCtr inclusive. --*/

   if (rbCtr < 1) {
      fprintf ( stderr,
                "%s: sorry, I couldn't find any block boundaries.\n",
                progName );
      exit(1);
   };

   fprintf ( stderr, "%s: splitting into blocks\n", progName );

   inFile = fopen ( inFileName, "rb" );
   if (inFile == NULL) {
      fprintf ( stderr, "%s: can't open `%s'\n", progName, inFileName );
      exit(1);
   }
   bsIn = bsOpenReadStream ( inFile );

   /*-- placate gcc's dataflow analyser --*/
   blockCRC = 0U; bsWr = 0;

   bitsRead = UINT64_C(0);
   outFile = NULL;
   wrBlock = 0;
   while (true) {
      b = bsGetBit(bsIn);
      if (b == 2) break;
      buffHi = (buffHi << 1) | (buffLo >> 31);
      buffLo = (buffLo << 1) | (b & 1);
      if (bitsRead == UINT64_C(47) + rbStart[wrBlock])
         blockCRC = (buffHi << 16) | (buffLo >> 16);

      if (outFile != NULL && bitsRead >= rbStart[wrBlock]
                          && bitsRead <= rbEnd[wrBlock]) {
         bsPutBit ( bsWr, b );
      }

      bitsRead++;

      if (bitsRead == rbEnd[wrBlock]+1) {
         if (outFile != NULL) {
            bsPutUChar ( bsWr, 0x17 ); bsPutUChar ( bsWr, 0x72 );
            bsPutUChar ( bsWr, 0x45 ); bsPutUChar ( bsWr, 0x38 );
            bsPutUChar ( bsWr, 0x50 ); bsPutUChar ( bsWr, 0x90 );
            bsPutUInt32 ( bsWr, blockCRC );
            bsClose ( bsWr );
            outFile = NULL;
         }
         if (wrBlock >= rbCtr) break;
         wrBlock++;
      } else
      if (bitsRead == rbStart[wrBlock]) {
         /* Create the output file name, correctly handling leading paths.
            (31.10.2001 by Sergey E. Kusikov) */
         char*   split;
         int32_t ofs, k;
         for (k = 0; k < BZ_MAX_FILENAME; k++)
            outFileName[k] = 0;
         strcpy (outFileName, inFileName);
         split = strrchr (outFileName, BZ_SPLIT_SYM);
         if (split == NULL) {
            split = outFileName;
         } else {
            ++split;
         }
         /* Now split points to the start of the basename. */
         ofs  = split - outFileName;
         sprintf (split, "rec%5d", wrBlock+1);
         for (p = split; *p != 0; p++) if (*p == ' ') *p = '0';
         strcat (outFileName, inFileName + ofs);

         if ( !endsInBz2(outFileName)) strcat ( outFileName, ".bz2" );

         fprintf ( stderr, "   writing block %d to `%s' ...\n",
                           wrBlock+1, outFileName );

         outFile = fopen_output_safely ( outFileName, "wb" );
         if (outFile == NULL) {
            fprintf ( stderr, "%s: can't write `%s'\n",
                      progName, outFileName );
            exit(1);
         }
         bsWr = bsOpenWriteStream ( outFile );
         bsPutUChar ( bsWr, BZ_HDR_B );
         bsPutUChar ( bsWr, BZ_HDR_Z );
         bsPutUChar ( bsWr, BZ_HDR_h );
         bsPutUChar ( bsWr, BZ_HDR_0 + 9 );
         bsPutUChar ( bsWr, 0x31 ); bsPutUChar ( bsWr, 0x41 );
         bsPutUChar ( bsWr, 0x59 ); bsPutUChar ( bsWr, 0x26 );
         bsPutUChar ( bsWr, 0x53 ); bsPutUChar ( bsWr, 0x59 );
      }
   }

   fprintf ( stderr, "%s: finished\n", progName );
   return 0;
}



/*-----------------------------------------------------------*/
/*--- end                                  bzip2recover.c ---*/
/*-----------------------------------------------------------*/
