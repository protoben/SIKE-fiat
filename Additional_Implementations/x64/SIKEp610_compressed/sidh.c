/********************************************************************************************
* Supersingular Isogeny Key Encapsulation Library
*
* Abstract: ephemeral supersingular isogeny Diffie-Hellman key exchange (SIDH)
*********************************************************************************************/ 

#include "random/random.h"
#include <stdio.h>


static void init_basis(digit_t *gen, f2elm_t XP, f2elm_t XQ, f2elm_t XR)
{ // Initialization of basis points
    
    fpcopy(gen,                  XP[0]);
    fpcopy(gen +   NWORDS_FIELD, XP[1]);
    fpcopy(gen + 2*NWORDS_FIELD, XQ[0]);
    fpcopy(gen + 3*NWORDS_FIELD, XQ[1]);
    fpcopy(gen + 4*NWORDS_FIELD, XR[0]);
    fpcopy(gen + 5*NWORDS_FIELD, XR[1]);
}


void random_mod_order_A(unsigned char* random_digits)
{  // Generation of Alice's secret key  
   // Outputs random value in [0, 2^eA - 1]

    memset(random_digits, 0, SECRETKEY_A_BYTES);
    randombytes(random_digits, SECRETKEY_A_BYTES);
    random_digits[0] &= 0xFE;                          // Make private scalar even
    random_digits[SECRETKEY_A_BYTES-1] &= MASK_ALICE;  // Masking last byte     
}


void random_mod_order_B(unsigned char* random_digits)
{  // Generation of Bob's secret key  
   // Outputs random value multiple of 3 in [0, 2^Floor(Log(2, oB)) - 1]

    memset(random_digits, 0, SECRETKEY_B_BYTES);
    randombytes(random_digits, SECRETKEY_B_BYTES);
    random_digits[SECRETKEY_B_BYTES-2] &= MASK3_BOB;     // Masking penultimate byte     
    random_digits[SECRETKEY_B_BYTES-1] &= MASK2_BOB;     // Masking last byte  
    
    mul3(random_digits); // make random_digits a multiple of 3
}


void FormatPrivKey_B(unsigned char *skB) {
    skB[SECRETKEY_B_BYTES-2] &= MASK3_BOB;
    skB[SECRETKEY_B_BYTES-1] &= MASK2_BOB; // clear necessary bits so that 3*ephemeralsk is still less than Bob_order
    mul3(skB); // multiply ephemeralsk by 3        
}


void PublicKeyCompression_A(const unsigned char* PublicKeyA, unsigned char* CompressedPKA)
{ // Alice's public key compression
  // It produces a compressed output that consists of three elements in Z_Bob_order and one field element
  // Input : Alice's public key PublicKeyA, which consists of 3 elements in GF(p^2).
  // Output: a compressed value CompressedPKA that consists of three elements in Z_Bob_order and one element in GF(p^2).                                                                         
    point_full_proj_t P, Q, phP, phQ, phX;
    publickey_t PK;
    digit_t inv[NWORDS_ORDER];
    f2elm_t A, vec[4], Zinv[4], one = {0};
    digit_t c0[NWORDS_ORDER] = {0}, d0[NWORDS_ORDER] = {0}, c1[NWORDS_ORDER] = {0}, d1[NWORDS_ORDER] = {0};
    digit_t temp[NWORDS_ORDER] = {0};
    unsigned int bit, rs[2] = {0};
    unsigned char mask = (unsigned char)-1;
    
    mask >>= (((ORDER_B_ENCODED_BYTES)*8) - OBOB_BITS);
    
    fpcopy((digit_t*)&Montgomery_one, one[0]);

    // Initialize images of Alice's basis
    fp2_decode(PublicKeyA, PK[0]);
    fp2_decode(PublicKeyA + FP2_ENCODED_BYTES, PK[1]);
    fp2_decode(PublicKeyA + 2*FP2_ENCODED_BYTES, PK[2]);
    
      
    recover_y(PK, phP, phQ, phX, A);

    BuildOrdinaryE3nBasis(A, P, Q, rs);
    
    fp2copy(phP->Z, vec[0]);
    fp2copy(phQ->Z, vec[1]);
     
    mont_n_way_inv(vec, 2, Zinv);
    
    fp2copy(one, P->Z);
    fp2copy(one, Q->Z);
    fp2mul_mont(phP->X, Zinv[0], phP->X);
    fp2mul_mont(phP->Y, Zinv[0], phP->Y);
    fp2copy(one, phP->Z);
    fp2mul_mont(phQ->X, Zinv[1], phQ->X);
    fp2mul_mont(phQ->Y, Zinv[1], phQ->Y);
    fp2copy(one, phQ->Z);

    ph3(phP, phQ, P, Q, A, c0, d0, c1, d1);
    
    bit = mod3(d1);
    to_Montgomery_mod_order(c0, c0, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);   // Converting to Montgomery representation
    to_Montgomery_mod_order(c1, c1, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);
    to_Montgomery_mod_order(d0, d0, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);
    to_Montgomery_mod_order(d1, d1, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);
    
    if (bit != 0) {  // Storing [d1*c0inv, c1*c0inv, d0*c0inv] and setting bit "NBITS_ORDER" to 0   
        Montgomery_inversion_mod_order_bingcd(d1, inv, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);
        Montgomery_neg(d0, (digit_t*)&Bob_order);
        Montgomery_multiply_mod_order(d0, inv, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        from_Montgomery_mod_order(temp, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);                    // Converting back from Montgomery representation
        memcpy(&CompressedPKA[0], temp, ORDER_B_ENCODED_BYTES);
        CompressedPKA[ORDER_B_ENCODED_BYTES-1] &= mask;
        Montgomery_neg(c1, (digit_t*)&Bob_order);
        Montgomery_multiply_mod_order(c1, inv, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        from_Montgomery_mod_order(temp, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        memcpy(&CompressedPKA[ORDER_B_ENCODED_BYTES], temp, ORDER_B_ENCODED_BYTES);
        CompressedPKA[2*ORDER_B_ENCODED_BYTES-1] &= mask;
        Montgomery_multiply_mod_order(c0, inv, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        from_Montgomery_mod_order(temp, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        memcpy(&CompressedPKA[2*ORDER_B_ENCODED_BYTES], temp, ORDER_B_ENCODED_BYTES);
        CompressedPKA[3*ORDER_B_ENCODED_BYTES-1] &= mask;
        CompressedPKA[3*ORDER_B_ENCODED_BYTES + FP2_ENCODED_BYTES] = 0x00;
    } else {  // Storing [d1*d0inv, c1*d0inv, c0*d0inv] and setting bit "NBITS_ORDER" to 1
        Montgomery_inversion_mod_order_bingcd(d0, inv, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);
        Montgomery_neg(d1, (digit_t*)&Bob_order);
        Montgomery_multiply_mod_order(d1, inv, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        from_Montgomery_mod_order(temp, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);                     // Converting back from Montgomery representation         
        memcpy(&CompressedPKA[0], temp, ORDER_B_ENCODED_BYTES);
        CompressedPKA[ORDER_B_ENCODED_BYTES-1] &= mask;
        Montgomery_multiply_mod_order(c1, inv, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        from_Montgomery_mod_order(temp, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        memcpy(&CompressedPKA[ORDER_B_ENCODED_BYTES], temp, ORDER_B_ENCODED_BYTES);
        CompressedPKA[2*ORDER_B_ENCODED_BYTES-1] &= mask;
        Montgomery_neg(c0, (digit_t*)&Bob_order);
        Montgomery_multiply_mod_order(c0, inv, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        from_Montgomery_mod_order(temp, temp, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        memcpy(&CompressedPKA[2*ORDER_B_ENCODED_BYTES], temp, ORDER_B_ENCODED_BYTES);
        CompressedPKA[3*ORDER_B_ENCODED_BYTES-1] &= mask;
        CompressedPKA[3*ORDER_B_ENCODED_BYTES + FP2_ENCODED_BYTES] = 0x80;
    }

    fp2_encode(A, &CompressedPKA[3*ORDER_B_ENCODED_BYTES]);
    
    CompressedPKA[3*ORDER_B_ENCODED_BYTES + FP2_ENCODED_BYTES] |= (unsigned char)rs[0];
    CompressedPKA[3*ORDER_B_ENCODED_BYTES + FP2_ENCODED_BYTES + 1] = (unsigned char)rs[1];
          
}


void PublicKeyCompression_B(const unsigned char* PublicKeyB, unsigned char* CompressedPKB)
{ // Bob's public key compression
  // It produces a compressed output that consists of three elements in Z_Alice_order, one element in GF(p^2) and 
  // Input : Bob's public key PublicKeyB, which consists of 3 elements in GF(p^2).
  // Output: a compressed value CompressedPKB that consists of three elements in Z_orderA and one element in GF(p^2). 
  // CurveIsogeny must be set up in advance using SIDH_curve_initialize().                                                       
    point_full_proj_t phP, phQ, phX;
    point_t S1, S2;
    publickey_t PK;
    f2elm_t A, vec[2], Zinv[2], one = {0};
    digit_t c0[NWORDS_ORDER] = {0}, d0[NWORDS_ORDER] = {0}, c1[NWORDS_ORDER] = {0}, d1[NWORDS_ORDER] = {0}, 
            tmp[2*NWORDS_ORDER] = {0}, inv[NWORDS_ORDER] = {0};
    unsigned char bit, r = 0;
    
    fpcopy((digit_t*)&Montgomery_one, one[0]);
     
    // Initialize images of Alice's basis
    fp2_decode(PublicKeyB, PK[0]);
    fp2_decode(PublicKeyB + FP2_ENCODED_BYTES, PK[1]);
    fp2_decode(PublicKeyB + 2*FP2_ENCODED_BYTES, PK[2]);
     
    recover_y(PK, phP, phQ, phX, A);
    
    fp2copy(phP->Z, vec[0]);
    fp2copy(phQ->Z, vec[1]);
    mont_n_way_inv(vec, 2, Zinv);
    fp2mul_mont(phP->X, Zinv[0], phP->X);
    fp2mul_mont(phP->Y, Zinv[0], phP->Y);
    fp2copy(one, phP->Z);
    fp2mul_mont(phQ->X, Zinv[1], phQ->X);
    fp2mul_mont(phQ->Y, Zinv[1], phQ->Y);
    fp2copy(one, phQ->Z);
    
    get_2_torsion_entangled_basis_compression(A, S1, S2, &bit, &r);
          
    ph2(phP, phQ, S1, S2, A, c0, d0, c1, d1);

    if ((d1[0] & 1) == 1) {  // Storing [-d0*d1^-1 = b1*a0^-1, -c1*d1^-1 = a1*a0^-1, c0*d1^-1 = b0*a0^-1] and setting bit384 to 0
        inv_mod_orderA(d1, inv);
        Montgomery_neg(d0, (digit_t*)Alice_order);
        multiply(d0, inv, tmp, NWORDS_ORDER);
        memcpy(&CompressedPKB[0], (unsigned char *)&tmp, ORDER_A_ENCODED_BYTES);
        CompressedPKB[ORDER_A_ENCODED_BYTES-1] &= MASK_ALICE;
        Montgomery_neg(c1, (digit_t*)Alice_order);
        multiply(c1, inv, tmp, NWORDS_ORDER);
        memcpy(&CompressedPKB[ORDER_A_ENCODED_BYTES], (unsigned char *)&tmp, ORDER_A_ENCODED_BYTES);
        CompressedPKB[2*ORDER_A_ENCODED_BYTES-1] &= MASK_ALICE;
        multiply(c0, inv, tmp, NWORDS_ORDER);
        memcpy(&CompressedPKB[2*ORDER_A_ENCODED_BYTES], (unsigned char *)&tmp, ORDER_A_ENCODED_BYTES);
        CompressedPKB[3*ORDER_A_ENCODED_BYTES-1] &= MASK_ALICE;
        CompressedPKB[3*ORDER_A_ENCODED_BYTES + FP2_ENCODED_BYTES] = 0x00;
    } else {  // Storing [ -d1*d0^-1 = b1*b0inv, c1*d0^-1 = a1*b0inv, -c0*d0^-1 = a0*b0inv] and setting bit384 to 1
        inv_mod_orderA(d0, inv);
        Montgomery_neg(d1, (digit_t*)Alice_order);
        multiply(d1, inv, tmp, NWORDS_ORDER);
        memcpy(&CompressedPKB[0], (unsigned char *)&tmp, ORDER_A_ENCODED_BYTES);
        CompressedPKB[ORDER_A_ENCODED_BYTES - 1] &= MASK_ALICE;
        multiply(c1, inv, tmp, NWORDS_ORDER);
        memcpy(&CompressedPKB[ORDER_A_ENCODED_BYTES], (unsigned char *)&tmp, ORDER_A_ENCODED_BYTES);
        CompressedPKB[2*ORDER_A_ENCODED_BYTES-1] &= MASK_ALICE;
        Montgomery_neg(c0, (digit_t*)Alice_order);
        multiply(c0, inv, tmp, NWORDS_ORDER);
        memcpy(&CompressedPKB[2*ORDER_A_ENCODED_BYTES], (unsigned char *)&tmp, ORDER_A_ENCODED_BYTES);
        CompressedPKB[3*ORDER_A_ENCODED_BYTES-1] &= MASK_ALICE;
        CompressedPKB[3*ORDER_A_ENCODED_BYTES + FP2_ENCODED_BYTES] = 0x80;
    }
    
    fp2_encode(A, &CompressedPKB[3*ORDER_A_ENCODED_BYTES]);
  
    CompressedPKB[3*ORDER_A_ENCODED_BYTES + FP2_ENCODED_BYTES] |= bit;
    CompressedPKB[3*ORDER_A_ENCODED_BYTES + FP2_ENCODED_BYTES + 1] = r;
}


int EphemeralKeyGeneration_Compressed_A(const unsigned char* PrivateKeyA, unsigned char* PublicKeyA)
{ // Alice's ephemeral public key generation
  // Input:  a private key PrivateKeyA in the range [0, 2^eA - 1]. 
  // Output: the public key PublicKeyA consisting of 3 elements in GF(p^2) which are encoded by removing leading 0 bytes.
    point_proj_t R, phiP = {0}, phiQ = {0}, phiR = {0}, pts[MAX_INT_POINTS_ALICE];
    f2elm_t XPA, XQA, XRA, coeff[3], A24plus = {0}, C24 = {0}, A = {0};
    unsigned int i, row, m, index = 0, pts_index[MAX_INT_POINTS_ALICE], npts = 0, ii = 0;
    unsigned char pk_temp[UNCOMPRESSEDPK_BYTES] = {0};

    // Initialize basis points
    init_basis((digit_t*)A_gen, XPA, XQA, XRA);
    init_basis((digit_t*)B_gen, phiP->X, phiQ->X, phiR->X);
    fpcopy((digit_t*)&Montgomery_one, (phiP->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, (phiQ->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, (phiR->Z)[0]);

    // Initialize constants: A24plus = A+2C, C24 = 4C, where A=6, C=1
    fpcopy((digit_t*)&Montgomery_one, A24plus[0]);
    fp2add(A24plus, A24plus, A24plus);
    fp2add(A24plus, A24plus, C24);
    fp2add(A24plus, C24, A);
    fp2add(C24, C24, A24plus);
    
    // Retrieve kernel point
    LADDER3PT(XPA, XQA, XRA, (digit_t*)PrivateKeyA, ALICE, R, A);
    
#if (OALICE_BITS % 2 == 1)
    point_proj_t S;

    xDBLe(R, S, A24plus, C24, (int)(OALICE_BITS-1));
    get_2_isog(S, A24plus, C24);
    eval_2_isog(phiP, S);
    eval_2_isog(phiQ, S);
    eval_2_isog(phiR, S);
    eval_2_isog(R, S);
#endif

    // Traverse tree
    index = 0;
    for (row = 1; row < MAX_Alice; row++) {
        while (index < MAX_Alice-row) {
            fp2copy(R->X, pts[npts]->X);
            fp2copy(R->Z, pts[npts]->Z);
            pts_index[npts++] = index;
            m = strat_Alice[ii++];
            xDBLe(R, R, A24plus, C24, (int)(2*m));
            index += m;
        }
        get_4_isog(R, A24plus, C24, coeff);

        for (i = 0; i < npts; i++) {
            eval_4_isog(pts[i], coeff);
        }
        eval_4_isog(phiP, coeff);
        eval_4_isog(phiQ, coeff);
        eval_4_isog(phiR, coeff);

        fp2copy(pts[npts-1]->X, R->X);
        fp2copy(pts[npts-1]->Z, R->Z);
        index = pts_index[npts-1];
        npts -= 1;
    }

    get_4_isog(R, A24plus, C24, coeff);
    eval_4_isog(phiP, coeff);
    eval_4_isog(phiQ, coeff);
    eval_4_isog(phiR, coeff);

    inv_3_way(phiP->Z, phiQ->Z, phiR->Z);
    fp2mul_mont(phiP->X, phiP->Z, phiP->X);
    fp2mul_mont(phiQ->X, phiQ->Z, phiQ->X);
    fp2mul_mont(phiR->X, phiR->Z, phiR->X);
                
    // Format public key                   
    fp2_encode(phiP->X, pk_temp);
    fp2_encode(phiQ->X, pk_temp + FP2_ENCODED_BYTES);
    fp2_encode(phiR->X, pk_temp + 2*FP2_ENCODED_BYTES);
    
    PublicKeyCompression_A(pk_temp, PublicKeyA);

    return 0;
}


int EphemeralKeyGeneration_Compressed_B(const unsigned char* PrivateKeyB, unsigned char* PublicKeyB)//CompressedPublicKeyB)
{ // Bob's ephemeral public key generation
  // Input:  a private key PrivateKeyB in the range [0, 2^Floor(Log(2,oB)) - 1]. 
  // Output: the public key PublicKeyB consisting of 3 elements in GF(p^2) which are encoded by removing leading 0 bytes.
    point_proj_t R, phiP = {0}, phiQ = {0}, phiR = {0}, pts[MAX_INT_POINTS_BOB];
    f2elm_t XPB, XQB, XRB, coeff[3], A24plus = {0}, A24minus = {0}, A = {0};
    unsigned int i, row, m, index = 0, pts_index[MAX_INT_POINTS_BOB], npts = 0, ii = 0;
    unsigned char ct_uncomp[UNCOMPRESSEDPK_BYTES] = {0};

    // Initialize basis points
    init_basis((digit_t*)B_gen, XPB, XQB, XRB);
    init_basis((digit_t*)A_gen, phiP->X, phiQ->X, phiR->X);
    fpcopy((digit_t*)&Montgomery_one, (phiP->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, (phiQ->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, (phiR->Z)[0]);

    // Initialize constants: A24minus = A-2C, A24plus = A+2C, where A=6, C=1
    fpcopy((digit_t*)&Montgomery_one, A24plus[0]);
    fp2add(A24plus, A24plus, A24plus);
    fp2add(A24plus, A24plus, A24minus);
    fp2add(A24plus, A24minus, A);
    fp2add(A24minus, A24minus, A24plus);
    
    // Retrieve kernel point
    LADDER3PT(XPB, XQB, XRB, (digit_t*)PrivateKeyB, BOB, R, A);
    
    // Traverse tree
    index = 0;
    for (row = 1; row < MAX_Bob; row++) {
        while (index < MAX_Bob-row) {
            fp2copy(R->X, pts[npts]->X);
            fp2copy(R->Z, pts[npts]->Z);
            pts_index[npts++] = index;
            m = strat_Bob[ii++];
            xTPLe(R, R, A24minus, A24plus, (int)m);
            index += m;
        } 
        get_3_isog(R, A24minus, A24plus, coeff);

        for (i = 0; i < npts; i++) {
            eval_3_isog(pts[i], coeff);
        }     
        eval_3_isog(phiP, coeff);
        eval_3_isog(phiQ, coeff);
        eval_3_isog(phiR, coeff);

        fp2copy(pts[npts-1]->X, R->X);
        fp2copy(pts[npts-1]->Z, R->Z);
        index = pts_index[npts-1];
        npts -= 1;
    }
    
    get_3_isog(R, A24minus, A24plus, coeff);
    eval_3_isog(phiP, coeff);
    eval_3_isog(phiQ, coeff);
    eval_3_isog(phiR, coeff);

    inv_3_way(phiP->Z, phiQ->Z, phiR->Z);
    fp2mul_mont(phiP->X, phiP->Z, phiP->X);
    fp2mul_mont(phiQ->X, phiQ->Z, phiQ->X);
    fp2mul_mont(phiR->X, phiR->Z, phiR->X);

    // Format public key
    fp2_encode(phiP->X, ct_uncomp);
    fp2_encode(phiQ->X, ct_uncomp + FP2_ENCODED_BYTES);
    fp2_encode(phiR->X, ct_uncomp + 2*FP2_ENCODED_BYTES);
    
    PublicKeyCompression_B(ct_uncomp, PublicKeyB);

    return 0;
}


void PublicKeyBDecompression_A(const unsigned char* SecretKeyA, const unsigned char* CompressedPKB, 
                               point_proj_t R, f2elm_t A)
{ // Bob's public key value decompression computed by Alice
  // Inputs: Alice's private key SecretKeyA, and
  //         Bob's compressed public key data CompressedPKB, which consists of three elements in Z_orderA and one element in GF(p^2).
  // Output: a point point_R in coordinates (X:Z) and the curve parameter param_A in GF(p^2). Outputs are stored in Montgomery representation.                                                                                         
    point_t S1 = {0}, S2 = {0};
    point_full_proj_t P = {0};
    //point_proj_t* R = (point_proj_t*)point_R;
    f2elm_t A24 = {0}, one = {0};
    digit_t tmp1[2*NWORDS_ORDER] = {0}, tmp2[2*NWORDS_ORDER] = {0}, vone[2*NWORDS_ORDER] = {0};
    digit_t SKin[NWORDS_ORDER] = {0}, comp_temp[NWORDS_ORDER] = {0};
    uint64_t mask = (digit_t)(-1);
    unsigned char bit, isASqr_r[2];
    
    mask >>= (MAXBITS_ORDER - OALICE_BITS);
    vone[0] = 1;
    fpcopy((digit_t*)&Montgomery_one, one[0]);

    fp2_decode(&CompressedPKB[3*ORDER_A_ENCODED_BYTES], A);
       
    bit = CompressedPKB[3*ORDER_A_ENCODED_BYTES + FP2_ENCODED_BYTES] >> 7;
    isASqr_r[0] = CompressedPKB[3*ORDER_A_ENCODED_BYTES + FP2_ENCODED_BYTES] & 0x1;
    isASqr_r[1] = CompressedPKB[3*ORDER_A_ENCODED_BYTES + FP2_ENCODED_BYTES + 1];
    
    get_2_torsion_entangled_basis_decompression(A, S1, S2, isASqr_r[0], isASqr_r[1]);
    
    fp2add(A, one, A24);
    fp2add(A24, one, A24);
    fp2div2(A24, A24);
    fp2div2(A24, A24);
       
    memcpy((unsigned char*)SKin, SecretKeyA, SECRETKEY_A_BYTES);
    if (bit == 0) {
        memcpy((unsigned char*)&comp_temp, &CompressedPKB[ORDER_A_ENCODED_BYTES], ORDER_A_ENCODED_BYTES);
        multiply((digit_t*)SKin, comp_temp, tmp1, NWORDS_ORDER);
        mp_add(tmp1, vone, tmp1, NWORDS_ORDER);
        tmp1[NWORDS_ORDER-1] &= (digit_t)mask;
        inv_mod_orderA(tmp1, tmp2);
        memcpy((unsigned char*)&comp_temp, &CompressedPKB[2*ORDER_A_ENCODED_BYTES], ORDER_A_ENCODED_BYTES);
        multiply((digit_t*)SKin, comp_temp, tmp1, NWORDS_ORDER);
        memcpy((unsigned char*)&comp_temp, &CompressedPKB[0], ORDER_A_ENCODED_BYTES);
        mp_add(&comp_temp[0], tmp1, tmp1, NWORDS_ORDER);
        multiply(tmp1, tmp2, vone, NWORDS_ORDER);
        vone[NWORDS_ORDER-1] &= (digit_t)mask;
        mont_twodim_scalarmult(vone, S1, S2, A, A24, P, OALICE_BITS);
    } else {
        memcpy((unsigned char*)&comp_temp, &CompressedPKB[2*ORDER_A_ENCODED_BYTES], ORDER_A_ENCODED_BYTES);
        multiply((digit_t*)SKin, comp_temp, tmp1, NWORDS_ORDER);
        mp_add(tmp1, vone, tmp1, NWORDS_ORDER);
        tmp1[NWORDS_ORDER-1] &= (digit_t)mask;
        inv_mod_orderA(tmp1, tmp2);
        memcpy((unsigned char*)&comp_temp, &CompressedPKB[ORDER_A_ENCODED_BYTES], ORDER_A_ENCODED_BYTES);
        multiply((digit_t*)SKin, comp_temp, tmp1, NWORDS_ORDER);
        memcpy((unsigned char*)&comp_temp, &CompressedPKB[0], ORDER_A_ENCODED_BYTES);
        mp_add(&comp_temp[0], tmp1, tmp1, NWORDS_ORDER);
        multiply(tmp1, tmp2, vone, NWORDS_ORDER);
        vone[NWORDS_ORDER-1] &= (digit_t)mask;
        mont_twodim_scalarmult(vone, S2, S1, A, A24, P, OALICE_BITS);
    }
    
    fp2copy(P->X, R->X);
    fp2copy(P->Z, R->Z);
    
    fp2div2(A,one);
    xTPLe_fast(R, R, one, OBOB_EXPON);
}


void PublicKeyADecompression_B(const unsigned char* SecretKeyB, const unsigned char* CompressedPKA, 
                               point_proj_t R, f2elm_t A)
{ // Alice's public key value decompression computed by Bob
  // Inputs: Bob's private key SecretKeyB, and
  //         Alice's compressed public key data CompressedPKA, which consists of three elements in Z_Bob_order and one element in GF(p^2),
  // Output: a point point_R in coordinates (X:Z) and the curve parameter param_A in GF(p^2). Outputs are stored in Montgomery representation.                                                                                                                           
    point_t R1, R2;
    //point_proj_t* R = (point_proj_t*)point_R;
    point_full_proj_t P, Q;
    f2elm_t A24, one = {0};
    digit_t t1[NWORDS_ORDER] = {0}, t2[NWORDS_ORDER] = {0}, t3[NWORDS_ORDER] = {0}, t4[NWORDS_ORDER] = {0}, 
            vone[NWORDS_ORDER] = {0}, temp[NWORDS_ORDER] = {0}, SKin[NWORDS_ORDER] = {0};
    unsigned char bit, rs[2];
    
    vone[0] = 1;
    to_Montgomery_mod_order(vone, vone, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);  // Converting to Montgomery representation
    
    fpcopy((digit_t*)&Montgomery_one, one[0]);
  
    fp2_decode(&CompressedPKA[3*ORDER_B_ENCODED_BYTES], A);
    
    bit = CompressedPKA[3*ORDER_B_ENCODED_BYTES + FP2_ENCODED_BYTES] >> 7;
    memcpy(rs, &CompressedPKA[3*ORDER_B_ENCODED_BYTES + FP2_ENCODED_BYTES], 2);
    rs[0] &= 0x7F;

    BuildOrdinaryE3nBasis_decompression(A, P, Q, rs[0], rs[1]);

    fp2copy(P->X,R1->x);
    fp2copy(P->Y,R1->y);
    fp2copy(Q->X,R2->x);
    fp2copy(Q->Y,R2->y);

    fp2add(A, one, A24);
    fp2add(A24, one, A24);
    fp2div2(A24, A24);
    fp2div2(A24, A24);
 
    memcpy((unsigned char*)SKin, SecretKeyB, SECRETKEY_B_BYTES);
    to_Montgomery_mod_order(SKin, t1, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);    // Converting to Montgomery representation 
    memcpy((unsigned char*)&temp, &CompressedPKA[0], ORDER_B_ENCODED_BYTES);
    to_Montgomery_mod_order(temp, t2, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);
    memcpy((unsigned char*)&temp, &CompressedPKA[ORDER_B_ENCODED_BYTES], ORDER_B_ENCODED_BYTES);
    to_Montgomery_mod_order(temp, t3, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);
    memcpy((unsigned char*)&temp, &CompressedPKA[2*ORDER_B_ENCODED_BYTES], ORDER_B_ENCODED_BYTES);
    to_Montgomery_mod_order(temp, t4, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);
    if (bit == 0) {    
        Montgomery_multiply_mod_order(t1, t3, t3, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        mp_add(t3, vone, t3, NWORDS_ORDER);
        Montgomery_inversion_mod_order_bingcd(t3, t3, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);
        Montgomery_multiply_mod_order(t1, t4, t4, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        mp_add(t2, t4, t4, NWORDS_ORDER);
        Montgomery_multiply_mod_order(t3, t4, t3, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        from_Montgomery_mod_order(t3, t3, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);    // Converting back from Montgomery representation        
        mont_twodim_scalarmult(t3, R1, R2, A, A24, P, OBOB_BITS);
    } else {   
        Montgomery_multiply_mod_order(t1, t4, t4, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        mp_add(t4, vone, t4, NWORDS_ORDER);
        Montgomery_inversion_mod_order_bingcd(t4, t4, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2, (digit_t*)&Montgomery_RB1);
        Montgomery_multiply_mod_order(t1, t3, t3, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        mp_add(t2, t3, t3, NWORDS_ORDER);
        Montgomery_multiply_mod_order(t3, t4, t3, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);
        from_Montgomery_mod_order(t3, t3, (digit_t*)Bob_order, (digit_t*)&Montgomery_RB2);    // Converting back from Montgomery representation 
        mont_twodim_scalarmult(t3, R2, R1, A, A24, P, OBOB_BITS);
    }

    fp2copy(P->X, R->X);
    fp2copy(P->Z, R->Z);
}


int EphemeralSecretAgreement_Compressed_A(const unsigned char* PrivateKeyA, const unsigned char* PKB, unsigned char* SharedSecretA)
{ // Alice's ephemeral shared secret computation
  // It produces a shared secret key SharedSecretA using her secret key PrivateKeyA and Bob's decompressed data point_R and param_A
  // Inputs: Alice's PrivateKeyA is an even integer in the range [2, oA-2], where oA = 2^OALICE_BITS. 
  //         Bob's decompressed data consists of point_R in (X:Z) coordinates and the curve parameter param_A in GF(p^2).
  // Output: a shared secret SharedSecretA that consists of one element in GF(p^2). 
    unsigned int i, ii = 0, row, m, index = 0, pts_index[MAX_INT_POINTS_ALICE], npts = 0;
    f2elm_t A24plus = {0}, C24 = {0};
    point_proj_t R, pts[MAX_INT_POINTS_ALICE];
    f2elm_t jinv, coeff[5], A;
    f2elm_t param_A = {0};
  
    if (PrivateKeyA == NULL || SharedSecretA == NULL) {
        return 0;
    }

    PublicKeyBDecompression_A(PrivateKeyA, PKB, R, param_A);
    
    fp2copy(param_A, A);
    
    fpadd((digit_t*)&Montgomery_one, (digit_t*)&Montgomery_one, C24[0]);
    fp2add(A, C24, A24plus);
    fpadd(C24[0], C24[0], C24[0]);

#if (OALICE_BITS % 2 == 1)
    point_proj_t S;

    xDBLe(R, S, A24plus, C24, (int)(OALICE_BITS-1));
    get_2_isog(S, A24plus, C24);
    eval_2_isog(R, S);
#endif

    // Traverse tree
    index = 0;
    for (row = 1; row < MAX_Alice; row++) {
        while (index < MAX_Alice-row) {
            fp2copy(R->X, pts[npts]->X);
            fp2copy(R->Z, pts[npts]->Z);
            pts_index[npts++] = index;
            m = strat_Alice[ii++];
            xDBLe(R, R, A24plus, C24, (int)(2*m));
            index += m;
        }
        get_4_isog(R, A24plus, C24, coeff);

        for (i = 0; i < npts; i++) {
            eval_4_isog(pts[i], coeff);
        }

        fp2copy(pts[npts-1]->X, R->X);
        fp2copy(pts[npts-1]->Z, R->Z);
        index = pts_index[npts-1];
        npts -= 1;
    }

    get_4_isog(R, A24plus, C24, coeff);
    fp2add(A24plus, A24plus, A24plus);
    fp2sub(A24plus, C24, A24plus);
    fp2add(A24plus, A24plus, A24plus);
    j_inv(A24plus, C24, jinv);
    
    fp2_encode(jinv, SharedSecretA);    // Format shared secret
    
    return 1;
}


int EphemeralSecretAgreement_Compressed_B(const unsigned char* PrivateKeyB, const unsigned char* PKA, unsigned char* SharedSecretB)
{ // Bob's ephemeral shared secret computation
  // It produces a shared secret key SharedSecretB using his secret key PrivateKeyB and Alice's decompressed data point_R and param_A
  // Inputs: Bob's PrivateKeyB is an integer in the range [1, oB-1], where oB = 3^OBOB_EXP. 
  //         Alice's decompressed data consists of point_R in (X:Z) coordinates and the curve parameter param_A in GF(p^2).
  // Output: a shared secret SharedSecretB that consists of one element in GF(p^2). 
    unsigned int i, ii = 0, row, m, index = 0, pts_index[MAX_INT_POINTS_BOB], npts = 0;
    f2elm_t A24plus = {0}, A24minus = {0};
    point_proj_t R, pts[MAX_INT_POINTS_BOB];
    f2elm_t jinv, A, coeff[3];
    f2elm_t param_A = {0};
   
    if (PrivateKeyB == NULL || SharedSecretB == NULL) {
        return 0;
    }    
    
    PublicKeyADecompression_B(PrivateKeyB, PKA, R, param_A);
    
    fp2copy((felm_t*)param_A, A);
    
    fpadd((digit_t*)&Montgomery_one, (digit_t*)&Montgomery_one, A24minus[0]);
    fp2add(A, A24minus, A24plus);
    fp2sub(A, A24minus, A24minus);
        
    // Traverse tree
    index = 0;
    for (row = 1; row < MAX_Bob; row++) {
        while (index < MAX_Bob-row) {
            fp2copy(R->X, pts[npts]->X);
            fp2copy(R->Z, pts[npts]->Z);
            pts_index[npts++] = index;
            m = strat_Bob[ii++];
            xTPLe(R, R, A24minus, A24plus, (int)m);
            index += m;
        }
        get_3_isog(R, A24minus, A24plus, coeff);

        for (i = 0; i < npts; i++) {
            eval_3_isog(pts[i], coeff);
        } 

        fp2copy(pts[npts-1]->X, R->X);
        fp2copy(pts[npts-1]->Z, R->Z);
        index = pts_index[npts-1];
        npts -= 1;
    }
     
    get_3_isog(R, A24minus, A24plus, coeff);
    fp2add(A24plus, A24minus, A);
    fp2add(A, A, A);
    fp2sub(A24plus, A24minus, A24plus);
    j_inv(A, A24plus, jinv);
    
    fp2_encode(jinv, SharedSecretB);    // Format shared secret
      
    return 1;
}

