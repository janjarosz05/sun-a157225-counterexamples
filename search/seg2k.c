// Segmented exhaustive search for odd m in [A,B) with NO representation
//   m = p + 2^x + K*2^y,  p prime, p = 5 (mod 6),  x,y >= 1        (OEIS A157225 for K = 7)
// Stage 1 (bit-sieve): bitmap P[k] = [6k+5 prime] on [a0-TMAX, a0+G); for each class c = m mod 6 and each
//   "small" term t <= TMAX with t = c-5 (mod 6), OR the bitmap shifted by (t-c+5)/6.  Zero bits = survivors.
// Stage 2 (exact): every survivor is re-checked against ALL terms t < m with a deterministic 64-bit
//   Miller-Rabin test.  Output lines "CE m" are counterexamples; "DONE a b survivors ce" closes each chunk.
// gcc -O3 -march=native -fopenmp seg2k.c -o seg2k -lm ;  ./seg2k A B [K=7] [G=1e11] [TBITS=34]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
static u64 mulmod(u64 a,u64 b,u64 m){ return (u128)a*b%m; }
static u64 powmod(u64 a,u64 e,u64 m){ u64 r=1; a%=m; while(e){ if(e&1) r=mulmod(r,a,m); a=mulmod(a,a,m); e>>=1; } return r; }
static int is_prime(u64 n){
  if(n<2) return 0;
  static const u64 sp[]={2,3,5,7,11,13,17,19,23,29,31,37};
  for(int i=0;i<12;i++){ if(n==sp[i]) return 1; if(n%sp[i]==0) return 0; }
  u64 d=n-1; int s=0; while(!(d&1)){ d>>=1; s++; }
  for(int i=0;i<12;i++){ u64 x=powmod(sp[i],d,n); if(x==1||x==n-1) continue; int c=1;
    for(int r=1;r<s;r++){ x=mulmod(x,x,n); if(x==n-1){ c=0; break; } } if(c) return 0; }
  return 1;
}
static u64 K=7;
static int has_rep(u64 m){           // exact, all terms
  for(u64 a=2;a<m;a<<=1) for(u64 b=2*K;a+b<m;b<<=1){ u64 r=m-a-b; if(r%6==5 && is_prime(r)) return 1; }
  return 0;
}
static u64 inv_mod(u64 a,u64 p){ int64_t t=0,nt=1,r=p,nr=a%p; while(nr){ int64_t q=r/nr,x; x=t-q*nt; t=nt; nt=x; x=r-q*nr; r=nr; nr=x; } if(t<0) t+=p; return t; }
int main(int argc,char**argv){
  u64 A=strtoull(argv[1],0,10), B=strtoull(argv[2],0,10);
  if(argc>3) K=strtoull(argv[3],0,10);
  u64 G=argc>4?(u64)atof(argv[4]):100000000000ULL; int TB=argc>5?atoi(argv[5]):34;
  u64 TMAX=1ULL<<TB;
  if(A<=TMAX+64){ fprintf(stderr,"A must exceed TMAX=2^%d\n",TB); return 1; }
  // small primes up to sqrt(B)
  u64 sq=(u64)sqrt((double)B)+2; char*sm=calloc(sq+1,1); u64 np=0;
  for(u64 i=2;i<=sq;i++){ if(!sm[i]){ np++; for(u64 j=i*i;j<=sq;j+=i) sm[j]=1; } }
  u64*pr=malloc(np*8),*off=malloc(np*8); np=0;
  for(u64 i=5;i<=sq;i++) if(!sm[i]){ pr[np]=i; off[np]=(i-(5%i))%i*inv_mod(6%i,i)%i; np++; } // k = off (mod p) <=> p | 6k+5
  free(sm);
  // terms by class
  u64*T[3]; int nT[3]={0,0,0}; for(int c=0;c<3;c++) T[c]=malloc(8*4096);
  for(u64 a=2;a<=TMAX;a<<=1) for(u64 b=2*K;a+b<=TMAX;b<<=1){ u64 t=a+b; for(int ci=0;ci<3;ci++){ int c=2*ci+1; if(t%6==(u64)((c+6-5)%6)) T[ci][nT[ci]++]=(t-c+5)/6; } }
  fprintf(stderr,"K=%llu primes=%llu terms %d %d %d\n",(unsigned long long)K,(unsigned long long)np,nT[0],nT[1],nT[2]);
  A-=A%6;
  for(u64 a0=A;a0<B;a0+=G){
    u64 a1=a0+G<B?a0+G:B; a1+= (6-a1%6)%6;
    u64 k0=(a0-TMAX)/6-1, k1=a1/6+1, NK=k1-k0, NW=(NK+63)/64+2;
    u64*P=aligned_alloc(64,NW*8); memset(P,0xff,NW*8);
    const u64 SEG=1ULL<<21;
    #pragma omp parallel for schedule(dynamic,4)
    for(u64 s0=0;s0<NK;s0+=SEG){
      u64 s1=s0+SEG<NK?s0+SEG:NK; u64 hi=6*(k0+s1)+5;
      for(u64 i=0;i<np;i++){ u64 p=pr[i]; if(p*p>hi) break;
        u64 kk=k0+s0; u64 r=kk%p; u64 k=kk+(off[i]+p-r)%p;       // first absolute k >= k0+s0 with p | 6k+5
        if(6*k+5==p) k+=p;
        for(u64 b=k-k0;b<s1;b+=p) P[b>>6]&=~(1ULL<<(b&63)); }
    }
    u64 j0=a0/6, j1=a1/6, NJW=(j1-j0+63)/64; u64 surv=0, ce=0;
    #pragma omp parallel for schedule(dynamic,4096) reduction(+:surv,ce)
    for(u64 w=0;w<NJW;w++){
      for(int ci=0;ci<3;ci++){
        u64 acc=0; u64 base=j0+64*w-k0; const u64*t=T[ci]; int n=nT[ci];
        for(int i=0;i<n && ~acc;i++){ u64 bit=base-t[i]; u64 q=bit>>6; int o=bit&63; u64 v=P[q]>>o; if(o) v|=P[q+1]<<(64-o); acc|=v; }
        u64 z=~acc;
        while(z){ int b=__builtin_ctzll(z); z&=z-1; u64 m=6*(j0+64*w+b)+2*ci+1; if(m<a0||m>=a1||m>=B) continue; surv++;
          if(!has_rep(m)){ ce++;
            #pragma omp critical
            { printf("CE %llu\n",(unsigned long long)m); fflush(stdout); } } }
      }
    }
    free(P);
    printf("DONE %llu %llu survivors=%llu ce=%llu\n",(unsigned long long)a0,(unsigned long long)(a1<B?a1:B),(unsigned long long)surv,(unsigned long long)ce); fflush(stdout);
  }
  return 0;
}
