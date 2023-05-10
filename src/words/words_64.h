/*
 *  Copyright (C) 2017 - This file is part of libecc project
 *
 *  Authors:
 *      Ryad BENADJILA <ryadbenadjila@gmail.com>
 *      Arnaud EBALARD <arnaud.ebalard@ssi.gouv.fr>
 *      Jean-Pierre FLORI <jean-pierre.flori@ssi.gouv.fr>
 *
 *  Contributors:
 *      Nicolas VIVET <nicolas.vivet@ssi.gouv.fr>
 *      Karim KHALFALLAH <karim.khalfallah@ssi.gouv.fr>
 *
 *  This software is licensed under a dual BSD and GPL v2 license.
 *  See LICENSE file at the root folder of the project.
 */
#ifndef __WORDS_64_H__
#define __WORDS_64_H__

/*
 * Types for 64-bit long words and a few useful macros.
 */

#include "types.h"

typedef uint64_t word_t;
typedef uint32_t hword_t;

/* WORD_BITS (resp. WORD_BYTES): number of bits (resp. bytes) in a word. */
#define WORD_BITS (64)
#define WORD_BYTES (WORD_BITS / 8)
#define HWORD_BITS (32)
#define HWORD_BYTES (HWORD_BITS / 8)

/* WORD: constant of word-size. */
#define WORD(A) (UINT64_C(A))
#define HWORD(A) (UINT32_C(A))

/* WORD_MAX: maximal value of a word. */
#define WORD_MAX UINT64_MAX
#define HWORD_MAX UINT32_MAX

/* PRINTF_WORD_HEX_FMT: printf hex format string for word */
#ifndef PRIx16
#define PRIx16 "hx"
#endif
#ifndef PRIx32
#define PRIx32 "lx"
#endif
#ifndef PRIx64
#ifndef __PRI_64_LENGTH_MODIFIER__
#define __PRI_64_LENGTH_MODIFIER__ "ll"
#endif
#define PRIx64 __PRI_64_LENGTH_MODIFIER__ "x"
#endif

#define PRINTF_WORD_HEX_FMT "%016" PRIx64

#ifndef PRIu16
#define PRIu16 "hu"
#endif
#ifndef PRIu32
#define PRIu32 "u"
#endif
#ifndef PRIu64
#define PRIu64 "llu"
#endif

#endif /* __WORDS_64_H__ */
