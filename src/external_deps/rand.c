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
#include "rand.h"

/* Unix and compatible case (including macOS) */
#if defined(WITH_STDLIB) && (defined(__unix__) || defined(__APPLE__))
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include "../words/words.h"

/*
 * Copy file content to buffer. Return 0 on success, i.e. if the request
 * size has been read and copied to buffer and -1 otherwise.
 */
static int fimport(unsigned char *buf, u16 buflen, const char *path)
{
	// u16 rem = buflen, copied = 0;
	// ssize_t ret;
	// int fd;

	// fd = open(path, O_RDONLY);
	// if (fd == -1) {
	// 	printf("Unable to open input file %s\n", path);
	// 	return -1;
	// }

	// while (rem) {
	// 	ret = (int)read(fd, buf + copied, rem);
	// 	if (ret <= 0) {
	// 		break;
	// 	} else {
	// 		rem -= (u16)ret;
	// 		copied += (u16)ret;
	// 	}
	// }

	// close(fd);

	// return (copied == buflen) ? 0 : -1;


	for (u16 i = 0; i < buflen; i++){
		buf[i] = i + (int)(*path);
	}

	return 0;
}

int get_random(unsigned char *buf, u16 len)
{
	return fimport(buf, len, "/dev/urandom");
}

/* Windows case */
#elif defined(WITH_STDLIB) && defined(__WIN32__)
#include <windows.h>
#include <wincrypt.h>

int get_random(unsigned char *buf, u16 len)
{
	HCRYPTPROV hCryptProv = 0;

	if (CryptAcquireContext(&hCryptProv, NULL, NULL,
				PROV_RSA_FULL, CRYPT_VERIFYCONTEXT) == FALSE) {
		return -1;
	}

	if (CryptGenRandom(hCryptProv, len, buf) == FALSE) {
		CryptReleaseContext(hCryptProv, 0);
		return -1;
	}
	CryptReleaseContext(hCryptProv, 0);
	return 0;
}

/* No platform detected, the user must provide an implementation! */
#else
/* WARNING: when providing/implementing the get_random function, one must:
 * 	- Use a proper entropy source with a TRNG (True Random Number Generator)
 *	basis and clean PRNG (Pseudo-Random Number Generator) post-processing
 *	when needed.
 *	- Use a non-leaking generator in contexts where attackers that have access
 *	to side channels are a plausible threat (a process in an OS sharing memory
 *	and caches with other possibly malicious processes, a microcontroller
 *	that can be observed using EM probes or power consumtion, ...).
 */
#error "rand.c: you have to implement get_random with a proper entropy source!"
#endif
