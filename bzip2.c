
/*-----------------------------------------------------------*/
/*--- A block-sorting, lossless compressor        bzip2.c ---*/
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


/*---------------------------------------------*/
/*--
  Some stuff for all platforms.
--*/

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <math.h>
#include <errno.h>
#include <ctype.h>
#include "bzlib.h"

#define ERROR_IF_EOF(i)       { if ((i) == EOF)  ioError(); }
#define ERROR_IF_NOT_ZERO(i)  { if ((i) != 0)    ioError(); }
#define ERROR_IF_MINUS_ONE(i) { if ((i) == (-1)) ioError(); }


/*---------------------------------------------*/
/*--
   Platform-specific stuff.
--*/

#if BZ_UNIX
#   include <fcntl.h>
#   include <sys/types.h>
#   include <utime.h>
#   include <unistd.h>
#   include <sys/stat.h>
#   include <sys/times.h>

#   define PATH_SEP    '/'
#   define MY_LSTAT    lstat
#   define MY_STAT     stat
#   define MY_S_ISREG  S_ISREG
#   define MY_S_ISDIR  S_ISDIR

#   define APPEND_FILESPEC(root, name) \
      root=snocString((root), (name))

#   define APPEND_FLAG(root, name) \
      root=snocString((root), (name))

#   define SET_BINARY_MODE(fd) /**/

#   ifdef __GNUC__
#      define NORETURN __attribute__ ((noreturn))
#   else
#      define NORETURN /**/
#   endif

#   ifdef __DJGPP__
#     include <io.h>
#     include <fcntl.h>
#     undef MY_LSTAT
#     undef MY_STAT
#     define MY_LSTAT stat
#     define MY_STAT stat
#     undef SET_BINARY_MODE
#     define SET_BINARY_MODE(fd)                        \
        do {                                            \
           int retVal = setmode ( fileno ( fd ),        \
                                  O_BINARY );           \
           ERROR_IF_MINUS_ONE ( retVal );               \
        } while ( 0 )
#   endif

#   ifdef __CYGWIN__
#     include <io.h>
#     include <fcntl.h>
#     undef SET_BINARY_MODE
#     define SET_BINARY_MODE(fd)                        \
        do {                                            \
           int retVal = setmode ( fileno ( fd ),        \
                                  O_BINARY );           \
           ERROR_IF_MINUS_ONE ( retVal );               \
        } while ( 0 )
#   endif
#endif /* BZ_UNIX */



#if BZ_LCCWIN32
#   include <io.h>
#   include <fcntl.h>
#   include <sys/stat.h>

#   define NORETURN       /**/
#   define PATH_SEP       '\\'
#   define MY_LSTAT       _stati64
#   define MY_STAT        _stati64
#   define MY_S_ISREG(x)  ((x) & _S_IFREG)
#   define MY_S_ISDIR(x)  ((x) & _S_IFDIR)

#   define APPEND_FLAG(root, name) \
      root=snocString((root), (name))

#   define APPEND_FILESPEC(root, name)                \
      root = snocString ((root), (name))

#   define SET_BINARY_MODE(fd)                        \
      do {                                            \
         int retVal = setmode ( fileno ( fd ),        \
                                O_BINARY );           \
         ERROR_IF_MINUS_ONE ( retVal );               \
      } while ( 0 )

#endif /* BZ_LCCWIN32 */

#if _WIN32
#define fileno          _fileno
#define write           _write
#define isatty          _isatty
#define setmode         _setmode
#define STDERR_FILENO   _fileno(stderr)
#endif

/*---------------------------------------------------*/
/*--- Misc (file handling) data decls             ---*/
/*---------------------------------------------------*/

int32_t   verbosity;
bool      keepInputFiles, smallMode, deleteOutputOnInterrupt;
bool      forceOverwrite, testFailsExist, unzFailsExist, noisy;
int32_t   numFileNames, numFilesProcessed, blockSize100k;
int32_t   exitValue;

/*-- source modes; F==file, I==stdin, O==stdout --*/
#define SM_I2O           1
#define SM_F2O           2
#define SM_F2F           3

/*-- operation modes --*/
#define OM_Z             1
#define OM_UNZ           2
#define OM_TEST          3

int32_t   opMode;
int32_t   srcMode;

#define FILE_NAME_LEN 1034

int32_t   longestFileName;
char      inName [FILE_NAME_LEN];
char      outName[FILE_NAME_LEN];
char      tmpName[FILE_NAME_LEN];
char*     progName;
char      progNameReally[FILE_NAME_LEN];
FILE*     outputHandleJustInCase;
int32_t   workFactor;

static void    panic                 ( const char* ) NORETURN;
static void    ioError               ( void )        NORETURN;
static void    outOfMemory           ( void )        NORETURN;
static void    configError           ( void )        NORETURN;
static void    crcError              ( void )        NORETURN;
static void    cleanUpAndFail        ( int32_t )     NORETURN;
static void    compressedStreamEOF   ( void )        NORETURN;

static void    copyFileName ( char*, const char* );
static void*   myMalloc     ( int32_t );
static void    applySavedFileAttrToOutputFile ( int fd );



/*---------------------------------------------------*/
/*--- An implementation of 64-bit ints.           ---*/
/*---------------------------------------------------*/

static
void uInt64_from_UInt32s ( uint64_t* n, uint32_t lo32, uint32_t hi32 )
{
   *n = ((uint64_t)hi32 << 32) & (uint64_t)lo32;
}


/* Divide *n by 10, and return the remainder.  */
static
char uInt64_qrm10 ( uint64_t* n )
{
   char rem = (int8_t)(*n % UINT64_C(10));
   *n /= UINT64_C(10);
   return rem;
}


/* ... and the Whole Entire Point of all this uint64_t stuff is
   so that we can supply the following function.
*/
static
void uInt64_toAscii ( char* outbuf, uint64_t* n )
{
   int32_t  i;
   char     buf[32];
   char     q;
   int32_t  nBuf   = 0;
   uint64_t n_copy = *n;
   do {
      q = uInt64_qrm10 ( &n_copy );
      buf[nBuf] = q + '0';
      nBuf++;
   } while (n_copy != UINT64_C(0));
   outbuf[nBuf] = 0;
   for (i = 0; i < nBuf; i++)
      outbuf[i] = buf[nBuf-i-1];
}


/*---------------------------------------------------*/
/*--- Processing of complete files and streams    ---*/
/*---------------------------------------------------*/

/*---------------------------------------------*/
static
bool myfeof ( FILE* f )
{
   int32_t c = fgetc ( f );
   if (c == EOF) return true;
   ungetc ( c, f );
   return false;
}


/*---------------------------------------------*/
static
void compressStream ( FILE* stream, FILE* zStream )
{
   BZFILE*   bzf = NULL;
   uint8_t   ibuf[5000];
   int32_t   nIbuf;
   uint32_t  nbytes_in_lo32, nbytes_in_hi32;
   uint32_t  nbytes_out_lo32, nbytes_out_hi32;
   int32_t   bzerr, bzerr_dummy, ret;

   SET_BINARY_MODE(stream);
   SET_BINARY_MODE(zStream);

   if (ferror(stream)) goto errhandler_io;
   if (ferror(zStream)) goto errhandler_io;

   bzf = BZ2_bzWriteOpen ( &bzerr, zStream,
                           blockSize100k, verbosity, workFactor );
   if (bzerr != BZ_OK) goto errhandler;

   if (verbosity >= 2) fprintf ( stderr, "\n" );

   while (true) {

      if (myfeof(stream)) break;
      nIbuf = fread ( ibuf, sizeof(uint8_t), 5000, stream );
      if (ferror(stream)) goto errhandler_io;
      if (nIbuf > 0) BZ2_bzWrite ( &bzerr, bzf, (void*)ibuf, nIbuf );
      if (bzerr != BZ_OK) goto errhandler;

   }

   BZ2_bzWriteClose64 ( &bzerr, bzf, 0,
                        &nbytes_in_lo32, &nbytes_in_hi32,
                        &nbytes_out_lo32, &nbytes_out_hi32 );
   if (bzerr != BZ_OK) goto errhandler;

   if (ferror(zStream)) goto errhandler_io;
   ret = fflush ( zStream );
   if (ret == EOF) goto errhandler_io;
   if (zStream != stdout) {
      int32_t fd = fileno ( zStream );
      if (fd < 0) goto errhandler_io;
      applySavedFileAttrToOutputFile ( fd );
      ret = fclose ( zStream );
      outputHandleJustInCase = NULL;
      if (ret == EOF) goto errhandler_io;
   }
   outputHandleJustInCase = NULL;
   if (ferror(stream)) goto errhandler_io;
   ret = fclose ( stream );
   if (ret == EOF) goto errhandler_io;

   if (verbosity >= 1) {
      if (nbytes_in_lo32 == 0 && nbytes_in_hi32 == 0) {
         fprintf ( stderr, " no data compressed.\n");
      } else {
         char   buf_nin[32], buf_nout[32];
         uint64_t nbytes_in,   nbytes_out;
         double nbytes_in_d, nbytes_out_d;
         uInt64_from_UInt32s ( &nbytes_in,
            nbytes_in_lo32, nbytes_in_hi32 );
         uInt64_from_UInt32s ( &nbytes_out,
            nbytes_out_lo32, nbytes_out_hi32 );
         nbytes_in_d  = (double)nbytes_in;
         nbytes_out_d = (double)nbytes_out;
         uInt64_toAscii ( buf_nin, &nbytes_in );
         uInt64_toAscii ( buf_nout, &nbytes_out );
         fprintf ( stderr, "%6.3f:1, %6.3f bits/byte, "
            "%5.2f%% saved, %s in, %s out.\n",
            nbytes_in_d / nbytes_out_d,
            (8.0 * nbytes_out_d) / nbytes_in_d,
            100.0 * (1.0 - nbytes_out_d / nbytes_in_d),
            buf_nin,
            buf_nout
         );
      }
   }

   return;

errhandler:
   BZ2_bzWriteClose64 ( &bzerr_dummy, bzf, 1,
                        &nbytes_in_lo32, &nbytes_in_hi32,
                        &nbytes_out_lo32, &nbytes_out_hi32 );
   switch (bzerr) {
      case BZ_CONFIG_ERROR:
         configError(); break;
      case BZ_MEM_ERROR:
         outOfMemory (); break;
      case BZ_IO_ERROR:
         errhandler_io:
         ioError(); break;
      default:
         panic ( "compress:unexpected error" );
   }

   panic ( "compress:end" );
   /*notreached*/
}



/*---------------------------------------------*/
static
bool uncompressStream ( FILE* zStream, FILE* stream )
{
   BZFILE*   bzf = NULL;
   int32_t   bzerr, bzerr_dummy, ret, nread, streamNo, i;
   uint8_t   obuf[5000];
   uint8_t   unused[BZ_MAX_UNUSED];
   int32_t   nUnused;
   void*     unusedTmpV;
   uint8_t*  unusedTmp;

   nUnused = 0;
   streamNo = 0;

   SET_BINARY_MODE(stream);
   SET_BINARY_MODE(zStream);

   if (ferror(stream)) goto errhandler_io;
   if (ferror(zStream)) goto errhandler_io;

   while (true) {

      bzf = BZ2_bzReadOpen (
               &bzerr, zStream, verbosity,
               (int)smallMode, unused, nUnused
            );
      if (bzf == NULL || bzerr != BZ_OK) goto errhandler;
      streamNo++;

      while (bzerr == BZ_OK) {
         nread = BZ2_bzRead ( &bzerr, bzf, obuf, 5000 );
         if (bzerr == BZ_DATA_ERROR_MAGIC) goto trycat;
         if ((bzerr == BZ_OK || bzerr == BZ_STREAM_END) && nread > 0)
            fwrite ( obuf, sizeof(uint8_t), nread, stream );
         if (ferror(stream)) goto errhandler_io;
      }
      if (bzerr != BZ_STREAM_END) goto errhandler;

      BZ2_bzReadGetUnused ( &bzerr, bzf, &unusedTmpV, &nUnused );
      if (bzerr != BZ_OK) panic ( "decompress:bzReadGetUnused" );

      unusedTmp = (uint8_t*)unusedTmpV;
      for (i = 0; i < nUnused; i++) unused[i] = unusedTmp[i];

      BZ2_bzReadClose ( &bzerr, bzf );
      if (bzerr != BZ_OK) panic ( "decompress:bzReadGetUnused" );

      if (nUnused == 0 && myfeof(zStream)) break;
   }

closeok:
   if (ferror(zStream)) goto errhandler_io;
   if (stream != stdout) {
      int32_t fd = fileno ( stream );
      if (fd < 0) goto errhandler_io;
      applySavedFileAttrToOutputFile ( fd );
   }
   ret = fclose ( zStream );
   if (ret == EOF) goto errhandler_io;

   if (ferror(stream)) goto errhandler_io;
   ret = fflush ( stream );
   if (ret != 0) goto errhandler_io;
   if (stream != stdout) {
      ret = fclose ( stream );
      outputHandleJustInCase = NULL;
      if (ret == EOF) goto errhandler_io;
   }
   outputHandleJustInCase = NULL;
   if (verbosity >= 2) fprintf ( stderr, "\n    " );
   return true;

trycat:
   if (forceOverwrite) {
      rewind(zStream);
      while (true) {
         if (myfeof(zStream)) break;
         nread = fread ( obuf, sizeof(uint8_t), 5000, zStream );
         if (ferror(zStream)) goto errhandler_io;
         if (nread > 0) fwrite ( obuf, sizeof(uint8_t), nread, stream );
         if (ferror(stream)) goto errhandler_io;
      }
      goto closeok;
   }

errhandler:
   BZ2_bzReadClose ( &bzerr_dummy, bzf );
   switch (bzerr) {
      case BZ_CONFIG_ERROR:
         configError(); break;
      case BZ_IO_ERROR:
         errhandler_io:
         ioError(); break;
      case BZ_DATA_ERROR:
         crcError();
      case BZ_MEM_ERROR:
         outOfMemory();
      case BZ_UNEXPECTED_EOF:
         compressedStreamEOF();
      case BZ_DATA_ERROR_MAGIC:
         if (zStream != stdin) fclose(zStream);
         if (stream != stdout) fclose(stream);
         if (streamNo == 1) {
            return false;
         } else {
            if (noisy)
            fprintf ( stderr,
                      "\n%s: %s: trailing garbage after EOF ignored\n",
                      progName, inName );
            return true;
         }
      default:
         panic ( "decompress:unexpected error" );
   }

   panic ( "decompress:end" );
   return true; /*notreached*/
}


/*---------------------------------------------*/
static
bool testStream ( FILE* zStream )
{
   BZFILE*   bzf = NULL;
   int32_t   bzerr, bzerr_dummy, ret, streamNo, i;
   uint8_t   obuf[5000];
   uint8_t   unused[BZ_MAX_UNUSED];
   int32_t   nUnused;
   void*     unusedTmpV;
   uint8_t*  unusedTmp;

   nUnused = 0;
   streamNo = 0;

   SET_BINARY_MODE(zStream);
   if (ferror(zStream)) goto errhandler_io;

   while (true) {

      bzf = BZ2_bzReadOpen (
               &bzerr, zStream, verbosity,
               (int)smallMode, unused, nUnused
            );
      if (bzf == NULL || bzerr != BZ_OK) goto errhandler;
      streamNo++;

      while (bzerr == BZ_OK) {
         BZ2_bzRead ( &bzerr, bzf, obuf, 5000 );
         if (bzerr == BZ_DATA_ERROR_MAGIC) goto errhandler;
      }
      if (bzerr != BZ_STREAM_END) goto errhandler;

      BZ2_bzReadGetUnused ( &bzerr, bzf, &unusedTmpV, &nUnused );
      if (bzerr != BZ_OK) panic ( "test:bzReadGetUnused" );

      unusedTmp = (uint8_t*)unusedTmpV;
      for (i = 0; i < nUnused; i++) unused[i] = unusedTmp[i];

      BZ2_bzReadClose ( &bzerr, bzf );
      if (bzerr != BZ_OK) panic ( "test:bzReadGetUnused" );
      if (nUnused == 0 && myfeof(zStream)) break;

   }

   if (ferror(zStream)) goto errhandler_io;
   ret = fclose ( zStream );
   if (ret == EOF) goto errhandler_io;

   if (verbosity >= 2) fprintf ( stderr, "\n    " );
   return true;

errhandler:
   BZ2_bzReadClose ( &bzerr_dummy, bzf );
   if (verbosity == 0)
      fprintf ( stderr, "%s: %s: ", progName, inName );
   switch (bzerr) {
      case BZ_CONFIG_ERROR:
         configError(); break;
      case BZ_IO_ERROR:
         errhandler_io:
         ioError(); break;
      case BZ_DATA_ERROR:
         fprintf ( stderr,
                   "data integrity (CRC) error in data\n" );
         return false;
      case BZ_MEM_ERROR:
         outOfMemory();
      case BZ_UNEXPECTED_EOF:
         fprintf ( stderr,
                   "file ends unexpectedly\n" );
         return false;
      case BZ_DATA_ERROR_MAGIC:
         if (zStream != stdin) fclose(zStream);
         if (streamNo == 1) {
          fprintf ( stderr,
                    "bad magic number (file not created by bzip2)\n" );
            return false;
         } else {
            if (noisy)
            fprintf ( stderr,
                      "trailing garbage after EOF ignored\n" );
            return true;
         }
      default:
         panic ( "test:unexpected error" );
   }

   panic ( "test:end" );
   return true; /*notreached*/
}


/*---------------------------------------------------*/
/*--- Error [non-] handling grunge                ---*/
/*---------------------------------------------------*/

/*---------------------------------------------*/
static
void setExit ( int32_t v )
{
   if (v > exitValue) exitValue = v;
}


/*---------------------------------------------*/
static
void cadvise ( void )
{
   if (noisy)
   fprintf (
      stderr,
      "\nIt is possible that the compressed file(s) have become corrupted.\n"
        "You can use the -tvv option to test integrity of such files.\n\n"
        "You can use the `bzip2recover' program to attempt to recover\n"
        "data from undamaged sections of corrupted files.\n\n"
    );
}


/*---------------------------------------------*/
static
void showFileNames ( void )
{
   if (noisy)
   fprintf (
      stderr,
      "\tInput file = %s, output file = %s\n",
      inName, outName
   );
}


/*---------------------------------------------*/
static
void cleanUpAndFail ( int32_t ec )
{
   int            retVal;
   struct MY_STAT statBuf;

   if ( srcMode == SM_F2F
        && opMode != OM_TEST
        && deleteOutputOnInterrupt ) {

      /* Check whether input file still exists.  Delete output file
         only if input exists to avoid loss of data.  Joerg Prante, 5
         January 2002.  (JRS 06-Jan-2002: other changes in 1.0.2 mean
         this is less likely to happen.  But to be ultra-paranoid, we
         do the check anyway.)  */
      retVal = MY_STAT ( inName, &statBuf );
      if (retVal == 0) {
         if (noisy)
            fprintf ( stderr,
                      "%s: Deleting output file %s, if it exists.\n",
                      progName, outName );
         if (outputHandleJustInCase != NULL)
            fclose ( outputHandleJustInCase );
         retVal = remove ( outName );
         if (retVal != 0)
            fprintf ( stderr,
                      "%s: WARNING: deletion of output file "
                      "(apparently) failed.\n",
                      progName );
      } else {
         fprintf ( stderr,
                   "%s: WARNING: deletion of output file suppressed\n",
                    progName );
         fprintf ( stderr,
                   "%s:    since input file no longer exists.  Output file\n",
                   progName );
         fprintf ( stderr,
                   "%s:    `%s' may be incomplete.\n",
                   progName, outName );
         fprintf ( stderr,
                   "%s:    I suggest doing an integrity test (bzip2 -tv)"
                   " of it.\n",
                   progName );
      }
   }

   if (noisy && numFileNames > 0 && numFilesProcessed < numFileNames) {
      fprintf ( stderr,
                "%s: WARNING: some files have not been processed:\n"
                "%s:    %d specified on command line, %d not processed yet.\n\n",
                progName, progName,
                numFileNames, numFileNames - numFilesProcessed );
   }
   setExit(ec);
   exit(exitValue);
}


/*---------------------------------------------*/
static
void panic ( const char* s )
{
   fprintf ( stderr,
             "\n%s: PANIC -- internal consistency error:\n"
             "\t%s\n"
             "\tThis is a BUG.  Please report it at:\n"
             "\thttps://gitlab.com/bzip2/bzip2/-/issues\n",
             progName, s );
   showFileNames();
   cleanUpAndFail( 3 );
}


/*---------------------------------------------*/
static
void crcError ( void )
{
   fprintf ( stderr,
             "\n%s: Data integrity error when decompressing.\n",
             progName );
   showFileNames();
   cadvise();
   cleanUpAndFail( 2 );
}


/*---------------------------------------------*/
static
void compressedStreamEOF ( void )
{
   if (noisy) {
      fprintf ( stderr,
         "\n%s: Compressed file ends unexpectedly;\n\t"
         "perhaps it is corrupted?  *Possible* reason follows.\n",
         progName );
      perror ( progName );
      showFileNames();
      cadvise();
   }
   cleanUpAndFail( 2 );
}


/*---------------------------------------------*/
static
void ioError ( void )
{
   fprintf ( stderr,
             "\n%s: I/O or other error, bailing out.  "
             "Possible reason follows.\n",
             progName );
   perror ( progName );
   showFileNames();
   cleanUpAndFail( 1 );
}


/*---------------------------------------------*/
static
void mySignalCatcher ( int n )
{
   fprintf ( stderr,
             "\n%s: Control-C or similar caught, quitting.\n",
             progName );
   cleanUpAndFail(1);
}


/*---------------------------------------------*/
static
void mySIGSEGVorSIGBUScatcher ( int n )
{
   const char* msg;
   if (opMode == OM_Z)
      msg = ": Caught a SIGSEGV or SIGBUS whilst compressing.\n"
      "\n"
      "   Possible causes are (most likely first):\n"
      "   (1) This computer has unreliable memory or cache hardware\n"
      "       (a surprisingly common problem; try a different machine.)\n"
      "   (2) A bug in the compiler used to create this executable\n"
      "       (unlikely, if you didn't compile bzip2 yourself.)\n"
      "   (3) A real bug in bzip2 -- I hope this should never be the case.\n"
      "   The user's manual, Section 4.3, has more info on (1) and (2).\n"
      "   \n"
      "   If you suspect this is a bug in bzip2, or are unsure about (1)\n"
      "   or (2), report it at: https://gitlab.com/bzip2/bzip2/-/issues\n"
      "   Section 4.3 of the user's manual describes the info a useful\n"
      "   bug report should have.  If the manual is available on your\n"
      "   system, please try and read it before mailing me.  If you don't\n"
      "   have the manual or can't be bothered to read it, mail me anyway.\n"
      "\n";
   else
      msg = ": Caught a SIGSEGV or SIGBUS whilst decompressing.\n"
      "\n"
      "   Possible causes are (most likely first):\n"
      "   (1) The compressed data is corrupted, and bzip2's usual checks\n"
      "       failed to detect this.  Try bzip2 -tvv my_file.bz2.\n"
      "   (2) This computer has unreliable memory or cache hardware\n"
      "       (a surprisingly common problem; try a different machine.)\n"
      "   (3) A bug in the compiler used to create this executable\n"
      "       (unlikely, if you didn't compile bzip2 yourself.)\n"
      "   (4) A real bug in bzip2 -- I hope this should never be the case.\n"
      "   The user's manual, Section 4.3, has more info on (2) and (3).\n"
      "   \n"
      "   If you suspect this is a bug in bzip2, or are unsure about (2)\n"
      "   or (3), report it at: https://gitlab.com/bzip2/bzip2/-/issues\n"
      "   Section 4.3 of the user's manual describes the info a useful\n"
      "   bug report should have.  If the manual is available on your\n"
      "   system, please try and read it before mailing me.  If you don't\n"
      "   have the manual or can't be bothered to read it, mail me anyway.\n"
      "\n";
   write ( STDERR_FILENO, "\n", 1 );
   write ( STDERR_FILENO, progName, strlen ( progName ) );
   write ( STDERR_FILENO, msg, strlen ( msg ) );

   msg = "\tInput file = ";
   write ( STDERR_FILENO, msg, strlen (msg) );
   write ( STDERR_FILENO, inName, strlen (inName) );
   write ( STDERR_FILENO, "\n", 1 );
   msg = "\tOutput file = ";
   write ( STDERR_FILENO, msg, strlen (msg) );
   write ( STDERR_FILENO, outName, strlen (outName) );
   write ( STDERR_FILENO, "\n", 1 );

   /* Don't call cleanupAndFail. If we ended up here something went
      terribly wrong. Trying to clean up might fail spectacularly. */

   if (opMode == OM_Z) setExit(3); else setExit(2);
   _exit(exitValue);
}


/*---------------------------------------------*/
static
void outOfMemory ( void )
{
   fprintf ( stderr,
             "\n%s: couldn't allocate enough memory\n",
             progName );
   showFileNames();
   cleanUpAndFail(1);
}


/*---------------------------------------------*/
static
void configError ( void )
{
   fprintf ( stderr,
             "bzip2: I'm not configured correctly for this platform!\n"
             "\tI require int32_t, int16_t and char to have sizes\n"
             "\tof 4, 2 and 1 bytes to run properly, and they don't.\n"
             "\tProbably you can fix this by defining them correctly,\n"
             "\tand recompiling.  Bye!\n" );
   setExit(3);
   exit(exitValue);
}


/*---------------------------------------------------*/
/*--- The main driver machinery                   ---*/
/*---------------------------------------------------*/

/* All rather crufty.  The main problem is that input files
   are stat()d multiple times before use.  This should be
   cleaned up.
*/

/*---------------------------------------------*/
static
void pad ( const char* s )
{
   int32_t i;
   if ( (int32_t)strlen(s) >= longestFileName ) return;
   for (i = 1; i <= longestFileName - (int32_t)strlen(s); i++)
      fprintf ( stderr, " " );
}


/*---------------------------------------------*/
static
void copyFileName ( char* to, const char* from )
{
   if ( strlen(from) > FILE_NAME_LEN-10 )  {
      fprintf (
         stderr,
         "bzip2: file name\n`%s'\n"
         "is suspiciously (more than %d chars) long.\n"
         "Try using a reasonable file name instead.  Sorry! :-)\n",
         from, FILE_NAME_LEN-10
      );
      setExit(1);
      exit(exitValue);
   }

  strncpy(to,from,FILE_NAME_LEN-10);
  to[FILE_NAME_LEN-10]='\0';
}


/*---------------------------------------------*/
static
bool fileExists ( const char* name )
{
   FILE *tmp   = fopen ( name, "rb" );
   bool exists = (tmp != NULL);
   if (tmp != NULL) fclose ( tmp );
   return exists;
}


/*---------------------------------------------*/
/* Open an output file safely with O_EXCL and good permissions.
   This avoids a race condition in versions < 1.0.2, in which
   the file was first opened and then had its interim permissions
   set safely.  We instead use open() to create the file with
   the interim permissions required. (--- --- rw-).

   For non-Unix platforms, if we are not worrying about
   security issues, simple this simply behaves like fopen.
*/
static
FILE* fopen_output_safely ( const char* name, const char* mode )
{
#  if BZ_UNIX
   FILE* fp;
   int   fh;
   fh = open(name, O_WRONLY|O_CREAT|O_EXCL, S_IWUSR|S_IRUSR);
   if (fh == -1) return NULL;
   fp = fdopen(fh, mode);
   if (fp == NULL) close(fh);
   return fp;
#  else
   return fopen(name, mode);
#  endif
}


/*---------------------------------------------*/
/*--
  if in doubt, return true
--*/
static
bool notAStandardFile ( const char* name )
{
   int            i;
   struct MY_STAT statBuf;

   i = MY_LSTAT ( name, &statBuf );
   if (i != 0) return true;
   if (MY_S_ISREG(statBuf.st_mode)) return false;
   return true;
}


/*---------------------------------------------*/
/*--
  rac 11/21/98 see if file has hard links to it
--*/
static
int32_t countHardLinks ( const char* name )
{
   int            i;
   struct MY_STAT statBuf;

   i = MY_LSTAT ( name, &statBuf );
   if (i != 0) return 0;
   return (statBuf.st_nlink - 1);
}


/*---------------------------------------------*/
/* Copy modification date, access date, permissions and owner from the
   source to destination file.  We have to copy this meta-info off
   into fileMetaInfo before starting to compress / decompress it,
   because doing it afterwards means we get the wrong access time.

   To complicate matters, in compress() and decompress() below, the
   sequence of tests preceding the call to saveInputFileMetaInfo()
   involves calling fileExists(), which in turn establishes its result
   by attempting to fopen() the file, and if successful, immediately
   fclose()ing it again.  So we have to assume that the fopen() call
   does not cause the access time field to be updated.

   Reading of the man page for stat() (man 2 stat) on RedHat 7.2 seems
   to imply that merely doing open() will not affect the access time.
   Therefore we merely need to hope that the C library only does
   open() as a result of fopen(), and not any kind of read()-ahead
   cleverness.

   It sounds pretty fragile to me.  Whether this carries across
   robustly to arbitrary Unix-like platforms (or even works robustly
   on this one, RedHat 7.2) is unknown to me.  Nevertheless ...
*/
#if BZ_UNIX
static
struct MY_STAT fileMetaInfo;
#endif

static
void saveInputFileMetaInfo ( const char* srcName )
{
#  if BZ_UNIX
   int retVal;
   /* Note use of stat here, not lstat. */
   retVal = MY_STAT( srcName, &fileMetaInfo );
   ERROR_IF_NOT_ZERO ( retVal );
#  endif
}


static
void applySavedTimeInfoToOutputFile ( const char* dstName )
{
#  if BZ_UNIX
   int      retVal;
   struct utimbuf uTimBuf;

   uTimBuf.actime = fileMetaInfo.st_atime;
   uTimBuf.modtime = fileMetaInfo.st_mtime;

   retVal = utime ( dstName, &uTimBuf );
   ERROR_IF_NOT_ZERO ( retVal );
#  endif
}

static
void applySavedFileAttrToOutputFile ( int fd )
{
#  if BZ_UNIX
   int retVal;

   retVal = fchmod ( fd, fileMetaInfo.st_mode );
   ERROR_IF_NOT_ZERO ( retVal );

   (void) fchown ( fd, fileMetaInfo.st_uid, fileMetaInfo.st_gid );
   /* chown() will in many cases return with EPERM, which can
      be safely ignored.
   */
#  endif
}


/*---------------------------------------------*/
static
bool containsDubiousChars ( const char* name )
{
#  if BZ_UNIX
   /* On unix, files can contain any characters and the file expansion
    * is performed by the shell.
    */
   return false;
#  else /* ! BZ_UNIX */
   /* On non-unix (Win* platforms), wildcard characters are not allowed in
    * filenames.
    */
   for (; *name != '\0'; name++)
      if (*name == '?' || *name == '*') return true;
   return false;
#  endif /* BZ_UNIX */
}


/*---------------------------------------------*/
#define BZ_N_SUFFIX_PAIRS 4

const char* zSuffix[BZ_N_SUFFIX_PAIRS]
   = { ".bz2", ".bz", ".tbz2", ".tbz" };
const char* unzSuffix[BZ_N_SUFFIX_PAIRS]
   = { "", "", ".tar", ".tar" };

static
bool hasSuffix ( const char* s, const char* suffix )
{
   int32_t ns = strlen(s);
   int32_t nx = strlen(suffix);
   if (ns < nx) return false;
   if (strcmp(s + ns - nx, suffix) == 0) return true;
   return false;
}

static
bool mapSuffix ( char* name,
                 const char* oldSuffix,
                 const char* newSuffix )
{
   if (!hasSuffix(name,oldSuffix)) return false;
   name[strlen(name)-strlen(oldSuffix)] = 0;
   strcat ( name, newSuffix );
   return true;
}


/*---------------------------------------------*/
static
void compress ( const char* name )
{
   FILE*   inStr;
   FILE*   outStr;
   int32_t n, i;
   struct MY_STAT statBuf;

   deleteOutputOnInterrupt = false;

   if (name == NULL && srcMode != SM_I2O)
      panic ( "compress: bad modes\n" );

   switch (srcMode) {
      case SM_I2O:
         copyFileName ( inName, (char*)"(stdin)" );
         copyFileName ( outName, (char*)"(stdout)" );
         break;
      case SM_F2F:
         copyFileName ( inName, name );
         copyFileName ( outName, name );
         strcat ( outName, ".bz2" );
         break;
      case SM_F2O:
         copyFileName ( inName, name );
         copyFileName ( outName, (char*)"(stdout)" );
         break;
   }

   if ( srcMode != SM_I2O && containsDubiousChars ( inName ) ) {
      if (noisy)
      fprintf ( stderr, "%s: There are no files matching `%s'.\n",
                progName, inName );
      setExit(1);
      return;
   }
   if ( srcMode != SM_I2O && !fileExists ( inName ) ) {
      fprintf ( stderr, "%s: Can't open input file %s: %s.\n",
                progName, inName, strerror(errno) );
      setExit(1);
      return;
   }
   for (i = 0; i < BZ_N_SUFFIX_PAIRS; i++) {
      if (hasSuffix(inName, zSuffix[i])) {
         if (noisy)
         fprintf ( stderr,
                   "%s: Input file %s already has %s suffix.\n",
                   progName, inName, zSuffix[i] );
         setExit(1);
         return;
      }
   }
   if ( srcMode == SM_F2F || srcMode == SM_F2O ) {
      MY_STAT(inName, &statBuf);
      if ( MY_S_ISDIR(statBuf.st_mode) ) {
         fprintf( stderr,
                  "%s: Input file %s is a directory.\n",
                  progName,inName);
         setExit(1);
         return;
      }
   }
   if ( srcMode == SM_F2F && !forceOverwrite && notAStandardFile ( inName )) {
      if (noisy)
      fprintf ( stderr, "%s: Input file %s is not a normal file.\n",
                progName, inName );
      setExit(1);
      return;
   }
   if ( srcMode == SM_F2F && fileExists ( outName ) ) {
      if (forceOverwrite) {
         remove(outName);
      } else {
         fprintf ( stderr, "%s: Output file %s already exists.\n",
            progName, outName );
         setExit(1);
         return;
      }
   }
   if ( srcMode == SM_F2F && !forceOverwrite &&
        (n=countHardLinks ( inName )) > 0) {
      fprintf ( stderr, "%s: Input file %s has %d other link%s.\n",
                progName, inName, n, n > 1 ? "s" : "" );
      setExit(1);
      return;
   }

   if ( srcMode == SM_F2F ) {
      /* Save the file's meta-info before we open it.  Doing it later
         means we mess up the access times. */
      saveInputFileMetaInfo ( inName );
   }

   switch ( srcMode ) {

      case SM_I2O:
         inStr = stdin;
         outStr = stdout;
         if ( isatty ( fileno ( stdout ) ) ) {
            fprintf ( stderr,
                      "%s: I won't write compressed data to a terminal.\n",
                      progName );
            fprintf ( stderr, "%s: For help, type: `%s --help'.\n",
                              progName, progName );
            setExit(1);
            return;
         };
         break;

      case SM_F2O:
         inStr = fopen ( inName, "rb" );
         outStr = stdout;
         if ( isatty ( fileno ( stdout ) ) ) {
            fprintf ( stderr,
                      "%s: I won't write compressed data to a terminal.\n",
                      progName );
            fprintf ( stderr, "%s: For help, type: `%s --help'.\n",
                              progName, progName );
            if ( inStr != NULL ) fclose ( inStr );
            setExit(1);
            return;
         };
         if ( inStr == NULL ) {
            fprintf ( stderr, "%s: Can't open input file %s: %s.\n",
                      progName, inName, strerror(errno) );
            setExit(1);
            return;
         };
         break;

      case SM_F2F:
         inStr = fopen ( inName, "rb" );
         outStr = fopen_output_safely ( outName, "wb" );
         if ( outStr == NULL) {
            fprintf ( stderr, "%s: Can't create output file %s: %s.\n",
                      progName, outName, strerror(errno) );
            if ( inStr != NULL ) fclose ( inStr );
            setExit(1);
            return;
         }
         if ( inStr == NULL ) {
            fprintf ( stderr, "%s: Can't open input file %s: %s.\n",
                      progName, inName, strerror(errno) );
            if ( outStr != NULL ) fclose ( outStr );
            setExit(1);
            return;
         };
         break;

      default:
         panic ( "compress: bad srcMode" );
         break;
   }

   if (verbosity >= 1) {
      fprintf ( stderr,  "  %s: ", inName );
      pad ( inName );
      fflush ( stderr );
   }

   /*--- Now the input and output handles are sane.  Do the Biz. ---*/
   outputHandleJustInCase = outStr;
   deleteOutputOnInterrupt = true;
   compressStream ( inStr, outStr );
   outputHandleJustInCase = NULL;

   /*--- If there was an I/O error, we won't get here. ---*/
   if ( srcMode == SM_F2F ) {
      applySavedTimeInfoToOutputFile ( outName );
      deleteOutputOnInterrupt = false;
      if ( !keepInputFiles ) {
         int retVal = remove ( inName );
         ERROR_IF_NOT_ZERO ( retVal );
      }
   }

   deleteOutputOnInterrupt = false;
}


/*---------------------------------------------*/
static
void uncompress ( const char* name )
{
   FILE*   inStr;
   FILE*   outStr;
   int32_t n, i;
   bool    magicNumberOK;
   bool    cantGuess;
   struct MY_STAT statBuf;

   deleteOutputOnInterrupt = false;

   if (name == NULL && srcMode != SM_I2O)
      panic ( "uncompress: bad modes\n" );

   cantGuess = false;
   switch (srcMode) {
      case SM_I2O:
         copyFileName ( inName, (char*)"(stdin)" );
         copyFileName ( outName, (char*)"(stdout)" );
         break;
      case SM_F2F:
         copyFileName ( inName, name );
         copyFileName ( outName, name );
         for (i = 0; i < BZ_N_SUFFIX_PAIRS; i++)
            if (mapSuffix(outName,zSuffix[i],unzSuffix[i]))
               goto zzz;
         cantGuess = true;
         strcat ( outName, ".out" );
         break;
      case SM_F2O:
         copyFileName ( inName, name );
         copyFileName ( outName, (char*)"(stdout)" );
         break;
   }

   zzz:
   if ( srcMode != SM_I2O && containsDubiousChars ( inName ) ) {
      if (noisy)
      fprintf ( stderr, "%s: There are no files matching `%s'.\n",
                progName, inName );
      setExit(1);
      return;
   }
   if ( srcMode != SM_I2O && !fileExists ( inName ) ) {
      fprintf ( stderr, "%s: Can't open input file %s: %s.\n",
                progName, inName, strerror(errno) );
      setExit(1);
      return;
   }
   if ( srcMode == SM_F2F || srcMode == SM_F2O ) {
      MY_STAT(inName, &statBuf);
      if ( MY_S_ISDIR(statBuf.st_mode) ) {
         fprintf( stderr,
                  "%s: Input file %s is a directory.\n",
                  progName,inName);
         setExit(1);
         return;
      }
   }
   if ( srcMode == SM_F2F && !forceOverwrite && notAStandardFile ( inName )) {
      if (noisy)
      fprintf ( stderr, "%s: Input file %s is not a normal file.\n",
                progName, inName );
      setExit(1);
      return;
   }
   if ( /* srcMode == SM_F2F implied && */ cantGuess ) {
      if (noisy)
      fprintf ( stderr,
                "%s: Can't guess original name for %s -- using %s\n",
                progName, inName, outName );
      /* just a warning, no return */
   }
   if ( srcMode == SM_F2F && fileExists ( outName ) ) {
      if (forceOverwrite) {
         remove(outName);
      } else {
         fprintf ( stderr, "%s: Output file %s already exists.\n",
                     progName, outName );
         setExit(1);
         return;
      }
   }
   if ( srcMode == SM_F2F && !forceOverwrite &&
        (n=countHardLinks ( inName ) ) > 0) {
      fprintf ( stderr, "%s: Input file %s has %d other link%s.\n",
                progName, inName, n, n > 1 ? "s" : "" );
      setExit(1);
      return;
   }

   if ( srcMode == SM_F2F ) {
      /* Save the file's meta-info before we open it.  Doing it later
         means we mess up the access times. */
      saveInputFileMetaInfo ( inName );
   }

   switch ( srcMode ) {

      case SM_I2O:
         inStr = stdin;
         outStr = stdout;
         if ( isatty ( fileno ( stdin ) ) ) {
            fprintf ( stderr,
                      "%s: I won't read compressed data from a terminal.\n",
                      progName );
            fprintf ( stderr, "%s: For help, type: `%s --help'.\n",
                              progName, progName );
            setExit(1);
            return;
         };
         break;

      case SM_F2O:
         inStr = fopen ( inName, "rb" );
         outStr = stdout;
         if ( inStr == NULL ) {
            fprintf ( stderr, "%s: Can't open input file %s:%s.\n",
                      progName, inName, strerror(errno) );
            if ( inStr != NULL ) fclose ( inStr );
            setExit(1);
            return;
         };
         break;

      case SM_F2F:
         inStr = fopen ( inName, "rb" );
         outStr = fopen_output_safely ( outName, "wb" );
         if ( outStr == NULL) {
            fprintf ( stderr, "%s: Can't create output file %s: %s.\n",
                      progName, outName, strerror(errno) );
            if ( inStr != NULL ) fclose ( inStr );
            setExit(1);
            return;
         }
         if ( inStr == NULL ) {
            fprintf ( stderr, "%s: Can't open input file %s: %s.\n",
                      progName, inName, strerror(errno) );
            if ( outStr != NULL ) fclose ( outStr );
            setExit(1);
            return;
         };
         break;

      default:
         panic ( "uncompress: bad srcMode" );
         break;
   }

   if (verbosity >= 1) {
      fprintf ( stderr, "  %s: ", inName );
      pad ( inName );
      fflush ( stderr );
   }

   /*--- Now the input and output handles are sane.  Do the Biz. ---*/
   outputHandleJustInCase = outStr;
   deleteOutputOnInterrupt = true;
   magicNumberOK = uncompressStream ( inStr, outStr );
   outputHandleJustInCase = NULL;

   /*--- If there was an I/O error, we won't get here. ---*/
   if ( magicNumberOK ) {
      if ( srcMode == SM_F2F ) {
         applySavedTimeInfoToOutputFile ( outName );
         deleteOutputOnInterrupt = false;
         if ( !keepInputFiles ) {
            int retVal = remove ( inName );
            ERROR_IF_NOT_ZERO ( retVal );
         }
      }
   } else {
      unzFailsExist = true;
      deleteOutputOnInterrupt = false;
      if ( srcMode == SM_F2F ) {
         int retVal = remove ( outName );
         ERROR_IF_NOT_ZERO ( retVal );
      }
   }
   deleteOutputOnInterrupt = false;

   if ( magicNumberOK ) {
      if (verbosity >= 1)
         fprintf ( stderr, "done\n" );
   } else {
      setExit(2);
      if (verbosity >= 1)
         fprintf ( stderr, "not a bzip2 file.\n" ); else
         fprintf ( stderr,
                   "%s: %s is not a bzip2 file.\n",
                   progName, inName );
   }

}


/*---------------------------------------------*/
static
void testf ( const char* name )
{
   FILE* inStr;
   bool  allOK;
   struct MY_STAT statBuf;

   deleteOutputOnInterrupt = false;

   if (name == NULL && srcMode != SM_I2O)
      panic ( "testf: bad modes\n" );

   copyFileName ( outName, (char*)"(none)" );
   switch (srcMode) {
      case SM_I2O: copyFileName ( inName, (char*)"(stdin)" ); break;
      case SM_F2F: copyFileName ( inName, name ); break;
      case SM_F2O: copyFileName ( inName, name ); break;
   }

   if ( srcMode != SM_I2O && containsDubiousChars ( inName ) ) {
      if (noisy)
      fprintf ( stderr, "%s: There are no files matching `%s'.\n",
                progName, inName );
      setExit(1);
      return;
   }
   if ( srcMode != SM_I2O && !fileExists ( inName ) ) {
      fprintf ( stderr, "%s: Can't open input %s: %s.\n",
                progName, inName, strerror(errno) );
      setExit(1);
      return;
   }
   if ( srcMode != SM_I2O ) {
      MY_STAT(inName, &statBuf);
      if ( MY_S_ISDIR(statBuf.st_mode) ) {
         fprintf( stderr,
                  "%s: Input file %s is a directory.\n",
                  progName,inName);
         setExit(1);
         return;
      }
   }

   switch ( srcMode ) {

      case SM_I2O:
         if ( isatty ( fileno ( stdin ) ) ) {
            fprintf ( stderr,
                      "%s: I won't read compressed data from a terminal.\n",
                      progName );
            fprintf ( stderr, "%s: For help, type: `%s --help'.\n",
                              progName, progName );
            setExit(1);
            return;
         };
         inStr = stdin;
         break;

      case SM_F2O: case SM_F2F:
         inStr = fopen ( inName, "rb" );
         if ( inStr == NULL ) {
            fprintf ( stderr, "%s: Can't open input file %s:%s.\n",
                      progName, inName, strerror(errno) );
            setExit(1);
            return;
         };
         break;

      default:
         panic ( "testf: bad srcMode" );
         break;
   }

   if (verbosity >= 1) {
      fprintf ( stderr, "  %s: ", inName );
      pad ( inName );
      fflush ( stderr );
   }

   /*--- Now the input handle is sane.  Do the Biz. ---*/
   outputHandleJustInCase = NULL;
   allOK = testStream ( inStr );

   if (allOK && verbosity >= 1) fprintf ( stderr, "ok\n" );
   if (!allOK) testFailsExist = true;
}


/*---------------------------------------------*/
static
void license ( void )
{
   fprintf ( stdout,

    "bzip2, a block-sorting file compressor.  "
    "Version %s.\n"
    "   \n"
    "   Copyright (C) 1996-2010 by Julian Seward.\n"
    "   \n"
    "   This program is free software; you can redistribute it and/or modify\n"
    "   it under the terms set out in the LICENSE file, which is included\n"
    "   in the bzip2-1.0.6 source distribution.\n"
    "   \n"
    "   This program is distributed in the hope that it will be useful,\n"
    "   but WITHOUT ANY WARRANTY; without even the implied warranty of\n"
    "   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n"
    "   LICENSE file for more details.\n"
    "   \n",
    BZ2_bzlibVersion()
   );
}


/*---------------------------------------------*/
static
void usage ( const char* fullProgName )
{
   fprintf (
      stderr,
      "bzip2, a block-sorting file compressor.  "
      "Version %s.\n"
      "\n   usage: %s [flags and input files in any order]\n"
      "\n"
      "   -h --help           print this message\n"
      "   -d --decompress     force decompression\n"
      "   -z --compress       force compression\n"
      "   -k --keep           keep (don't delete) input files\n"
      "   -f --force          overwrite existing output files\n"
      "   -t --test           test compressed file integrity\n"
      "   -c --stdout         output to standard out\n"
      "   -q --quiet          suppress noncritical error messages\n"
      "   -v --verbose        be verbose (a 2nd -v gives more)\n"
      "   -L --license        display software version & license\n"
      "   -V --version        display software version & license\n"
      "   -s --small          use less memory (at most 2500k)\n"
      "   -1 .. -9            set block size to 100k .. 900k\n"
      "   --fast              alias for -1\n"
      "   --best              alias for -9\n"
      "\n"
      "   If invoked as `bzip2', default action is to compress.\n"
      "              as `bunzip2',  default action is to decompress.\n"
      "              as `bzcat', default action is to decompress to stdout.\n"
      "\n"
      "   If no file names are given, bzip2 compresses or decompresses\n"
      "   from standard input to standard output.  You can combine\n"
      "   short flags, so `-v -4' means the same as -v4 or -4v, &c.\n"
#     if BZ_UNIX
      "\n"
#     endif
      ,

      BZ2_bzlibVersion(),
      fullProgName
   );
}


/*---------------------------------------------*/
static
void redundant ( const char* flag )
{
   fprintf (
      stderr,
      "%s: %s is redundant in versions 0.9.5 and above\n",
      progName, flag );
}


/*---------------------------------------------*/
/*--
  All the garbage from here to main() is purely to
  implement a linked list of command-line arguments,
  into which main() copies argv[1 .. argc-1].

  The purpose of this exercise is to facilitate
  the expansion of wildcard characters * and ? in
  filenames for OSs which don't know how to do it
  themselves, like MSDOS, Windows 95 and NT.

  The actual Dirty Work is done by the platform-
  specific macro APPEND_FILESPEC.
--*/

typedef
   struct zzzz {
      char*        name;
      struct zzzz* link;
   }
   Cell;


/*---------------------------------------------*/
static
void *myMalloc ( int32_t n )
{
   void* p;

   p = malloc ( (size_t)n );
   if (p == NULL) outOfMemory ();
   return p;
}


/*---------------------------------------------*/
static
Cell *mkCell ( void )
{
   Cell *c;

   c = (Cell*) myMalloc ( sizeof ( Cell ) );
   c->name = NULL;
   c->link = NULL;
   return c;
}


/*---------------------------------------------*/
static
Cell *snocString ( Cell* root, const char* name )
{
   if (root == NULL) {
      Cell *tmp = mkCell();
      tmp->name = (char*) myMalloc ( 5 + strlen(name) );
      strcpy ( tmp->name, name );
      return tmp;
   } else {
      Cell *tmp = root;
      while (tmp->link != NULL) tmp = tmp->link;
      tmp->link = snocString ( tmp->link, name );
      return root;
   }
}


/*---------------------------------------------*/
static
void addFlagsFromEnvVar ( Cell** argList, const char* varName )
{
   int32_t i, j, k;
   char   *envbase, *p;

   envbase = getenv(varName);
   if (envbase != NULL) {
      p = envbase;
      i = 0;
      while (true) {
         if (p[i] == 0) break;
         p += i;
         i = 0;
         while (isspace((int32_t)(p[0]))) p++;
         while (p[i] != 0 && !isspace((int32_t)(p[i]))) i++;
         if (i > 0) {
            k = i; if (k > FILE_NAME_LEN-10) k = FILE_NAME_LEN-10;
            for (j = 0; j < k; j++) tmpName[j] = p[j];
            tmpName[k] = 0;
            APPEND_FLAG(*argList, tmpName);
         }
      }
   }
}


/*---------------------------------------------*/
#define ISFLAG(s) (strcmp(aa->name, (s))==0)

int main ( int argc, char *argv[] )
{
   int32_t  i, j;
   char    *tmp;
   Cell    *argList;
   Cell    *aa;
   bool     decode;

   /*-- Be really really really paranoid :-) --*/
   if (sizeof(int32_t) != 4 || sizeof(uint32_t) != 4  ||
       sizeof(int16_t) != 2 || sizeof(uint16_t) != 2  ||
       sizeof(char)  != 1 || sizeof(uint8_t)  != 1)
      configError();

   /*-- Initialise --*/
   outputHandleJustInCase  = NULL;
   smallMode               = false;
   keepInputFiles          = false;
   forceOverwrite          = false;
   noisy                   = true;
   verbosity               = 0;
   blockSize100k           = 9;
   testFailsExist          = false;
   unzFailsExist           = false;
   numFileNames            = 0;
   numFilesProcessed       = 0;
   workFactor              = 30;
   deleteOutputOnInterrupt = false;
   exitValue               = 0;
   i = j = 0; /* avoid bogus warning from egcs-1.1.X */

   /*-- Set up signal handlers for mem access errors --*/
   signal (SIGSEGV, mySIGSEGVorSIGBUScatcher);
#  if BZ_UNIX
#  ifndef __DJGPP__
   signal (SIGBUS,  mySIGSEGVorSIGBUScatcher);
#  endif
#  endif

   copyFileName ( inName,  (char*)"(none)" );
   copyFileName ( outName, (char*)"(none)" );

   copyFileName ( progNameReally, argv[0] );
   progName = &progNameReally[0];
   for (tmp = &progNameReally[0]; *tmp != '\0'; tmp++)
      if (*tmp == PATH_SEP) progName = tmp + 1;


   /*-- Copy flags from env var BZIP2, and
        expand filename wildcards in arg list.
   --*/
   argList = NULL;
   addFlagsFromEnvVar ( &argList,  (char*)"BZIP2" );
   addFlagsFromEnvVar ( &argList,  (char*)"BZIP" );
   for (i = 1; i <= argc-1; i++)
      APPEND_FILESPEC(argList, argv[i]);


   /*-- Find the length of the longest filename --*/
   longestFileName = 7;
   numFileNames    = 0;
   decode          = true;
   for (aa = argList; aa != NULL; aa = aa->link) {
      if (ISFLAG("--")) { decode = false; continue; }
      if (aa->name[0] == '-' && decode) continue;
      numFileNames++;
      if (longestFileName < (int32_t)strlen(aa->name) )
         longestFileName = (int32_t)strlen(aa->name);
   }


   /*-- Determine source modes; flag handling may change this too. --*/
   if (numFileNames == 0)
      srcMode = SM_I2O; else srcMode = SM_F2F;


   /*-- Determine what to do (compress/uncompress/test/cat). --*/
   /*-- Note that subsequent flag handling may change this. --*/
   opMode = OM_Z;

   if ( (strstr ( progName, "unzip" ) != 0) ||
        (strstr ( progName, "UNZIP" ) != 0) )
      opMode = OM_UNZ;

   if ( (strstr ( progName, "z2cat" ) != 0) ||
        (strstr ( progName, "Z2CAT" ) != 0) ||
        (strstr ( progName, "zcat" ) != 0)  ||
        (strstr ( progName, "ZCAT" ) != 0) )  {
      opMode = OM_UNZ;
      srcMode = (numFileNames == 0) ? SM_I2O : SM_F2O;
   }


   /*-- Look at the flags. --*/
   for (aa = argList; aa != NULL; aa = aa->link) {
      if (ISFLAG("--")) break;
      if (aa->name[0] == '-' && aa->name[1] != '-') {
         for (j = 1; aa->name[j] != '\0'; j++) {
            switch (aa->name[j]) {
               case 'c': srcMode          = SM_F2O; break;
               case 'd': opMode           = OM_UNZ; break;
               case 'z': opMode           = OM_Z; break;
               case 'f': forceOverwrite   = true; break;
               case 't': opMode           = OM_TEST; break;
               case 'k': keepInputFiles   = true; break;
               case 's': smallMode        = true; break;
               case 'q': noisy            = false; break;
               case '1': blockSize100k    = 1; break;
               case '2': blockSize100k    = 2; break;
               case '3': blockSize100k    = 3; break;
               case '4': blockSize100k    = 4; break;
               case '5': blockSize100k    = 5; break;
               case '6': blockSize100k    = 6; break;
               case '7': blockSize100k    = 7; break;
               case '8': blockSize100k    = 8; break;
               case '9': blockSize100k    = 9; break;
               case 'V':
               case 'L': license();
                         exit ( 0 );
                         break;
               case 'v': verbosity++; break;
               case 'h': usage ( progName );
                         exit ( 0 );
                         break;
               default:  fprintf ( stderr, "%s: Bad flag `%s'\n",
                                   progName, aa->name );
                         usage ( progName );
                         exit ( 1 );
                         break;
            }
         }
      }
   }

   /*-- And again ... --*/
   for (aa = argList; aa != NULL; aa = aa->link) {
      if (ISFLAG("--")) break;
      if (ISFLAG("--stdout"))            srcMode          = SM_F2O;  else
      if (ISFLAG("--decompress"))        opMode           = OM_UNZ;  else
      if (ISFLAG("--compress"))          opMode           = OM_Z;    else
      if (ISFLAG("--force"))             forceOverwrite   = true;    else
      if (ISFLAG("--test"))              opMode           = OM_TEST; else
      if (ISFLAG("--keep"))              keepInputFiles   = true;    else
      if (ISFLAG("--small"))             smallMode        = true;    else
      if (ISFLAG("--quiet"))             noisy            = false;   else
      if (ISFLAG("--version"))           { license(); exit ( 0 ); }  else
      if (ISFLAG("--license"))           { license(); exit ( 0 ); }  else
      if (ISFLAG("--exponential"))       workFactor = 1;             else
      if (ISFLAG("--repetitive-best"))   redundant(aa->name);        else
      if (ISFLAG("--repetitive-fast"))   redundant(aa->name);        else
      if (ISFLAG("--fast"))              blockSize100k = 1;          else
      if (ISFLAG("--best"))              blockSize100k = 9;          else
      if (ISFLAG("--verbose"))           verbosity++;                else
      if (ISFLAG("--help"))              { usage ( progName ); exit ( 0 ); }
         else
         if (strncmp ( aa->name, "--", 2) == 0) {
            fprintf ( stderr, "%s: Bad flag `%s'\n", progName, aa->name );
            usage ( progName );
            exit ( 1 );
         }
   }

   if (verbosity > 4) verbosity = 4;
   if (opMode == OM_Z && smallMode && blockSize100k > 2)
      blockSize100k = 2;

   if (opMode == OM_TEST && srcMode == SM_F2O) {
      fprintf ( stderr, "%s: -c and -t cannot be used together.\n",
                progName );
      exit ( 1 );
   }

   if (srcMode == SM_F2O && numFileNames == 0)
      srcMode = SM_I2O;

   if (opMode != OM_Z) blockSize100k = 0;

   if (srcMode == SM_F2F) {
      signal (SIGINT,  mySignalCatcher);
      signal (SIGTERM, mySignalCatcher);
#     if BZ_UNIX
      signal (SIGHUP,  mySignalCatcher);
#     endif
   }

   if (opMode == OM_Z) {
      if (srcMode == SM_I2O) {
         compress ( NULL );
      } else {
         decode = true;
         for (aa = argList; aa != NULL; aa = aa->link) {
            if (ISFLAG("--")) { decode = false; continue; }
            if (aa->name[0] == '-' && decode) continue;
            numFilesProcessed++;
            compress ( aa->name );
         }
      }
   }
   else

   if (opMode == OM_UNZ) {
      unzFailsExist = false;
      if (srcMode == SM_I2O) {
         uncompress ( NULL );
      } else {
         decode = true;
         for (aa = argList; aa != NULL; aa = aa->link) {
            if (ISFLAG("--")) { decode = false; continue; }
            if (aa->name[0] == '-' && decode) continue;
            numFilesProcessed++;
            uncompress ( aa->name );
         }
      }
      if (unzFailsExist) {
         setExit(2);
         exit(exitValue);
      }
   }

   else {
      testFailsExist = false;
      if (srcMode == SM_I2O) {
         testf ( NULL );
      } else {
         decode = true;
         for (aa = argList; aa != NULL; aa = aa->link) {
            if (ISFLAG("--")) { decode = false; continue; }
            if (aa->name[0] == '-' && decode) continue;
            numFilesProcessed++;
            testf ( aa->name );
         }
      }
      if (testFailsExist) {
         if (noisy) {
            fprintf ( stderr,
              "\n"
              "You can use the `bzip2recover' program to attempt to recover\n"
              "data from undamaged sections of corrupted files.\n\n"
            );
         }
         setExit(2);
         exit(exitValue);
      }
   }

   /* Free the argument list memory to mollify leak detectors
      (eg) Purify, Checker.  Serves no other useful purpose.
   */
   aa = argList;
   while (aa != NULL) {
      Cell* aa2 = aa->link;
      if (aa->name != NULL) free(aa->name);
      free(aa);
      aa = aa2;
   }

   return exitValue;
}


/*-----------------------------------------------------------*/
/*--- end                                         bzip2.c ---*/
/*-----------------------------------------------------------*/
