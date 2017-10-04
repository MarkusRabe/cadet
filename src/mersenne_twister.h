//
//  mersenne_twister.h
//  cadet
//
//  Created by Markus Rabe on 03.10.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef mersenne_twister_h
#define mersenne_twister_h

/* initializes mt[N] with a seed. Default seed is 5489UL. */
void init_genrand(unsigned long s);

/* generates a random number on [0,0xffffffff]-interval */
unsigned long genrand_int32(void);

/* generates a random number on [0,0x7fffffff]-interval */
long genrand_int31(void);

#endif /* mersenne_twister_h */
