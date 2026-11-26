// Bit-sieve scan for m = p + 2^x + K*2^y, x,y>=1, p prime.
//   RES=1 or 5: p ≡ RES (mod 6);  RES=0: p any prime >= 5 (check p = 3 separately).
// Bitmaps PB[R][k] = [6k+R is prime], k < B/6+1. For the class c = m mod 6, m = 6j+c:
//   r = m - t = 6k+R  <=>  t ≡ c-R (mod 6), k = j - (t - c + R)/6.
// found[j] = OR_t PB[R][j - s_t]  (bit shifts).  Prints "K m" for every m without a representation.
// gcc -O3 -march=native -fopenmp sieve2k.c -o sieve2k -lm ; ./sieve2k RES B K1 [K2 ...]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64;
static u64 *PB[6]; static u64 NK, NW;
static inline u64 word_at(const u64*P,int64_t bit){
  if(bit>=0){ u64 w=bit>>6; int o=bit&63; u64 lo=P[w]>>o; if(o && w+1<NW) lo|=P[w+1]<<(64-o); return lo; }
  if(bit<=-64) return 0;
  return P[0]<<(-bit);
}
static u64 inv_mod(u64 a,u64 p){ int64_t t=0,nt=1,r=p,nr=a%p; while(nr){ int64_t q=r/nr,x; x=t-q*nt; t=nt; nt=x; x=r-q*nr; r=nr; nr=x; } if(t<0) t+=p; return t; }
static void build(int R,u64 B,u64*pr,int np){
  u64*P=aligned_alloc(64,NW*8); memset(P,0xff,NW*8);
  if(R==1) P[0]&=~1ULL; // 1 is not prime
  const u64 SEG=1ULL<<22;
  #pragma omp parallel for schedule(dynamic,1)
  for(u64 s0=0;s0<NK;s0+=SEG){
    u64 s1=s0+SEG<NK?s0+SEG:NK;
    for(int i=0;i<np;i++){ u64 p=pr[i]; if(p*p>6*s1+R) break;
      u64 k=(p-(R%p))%p*inv_mod(6%p,p)%p;
      if(k<s0) k+=(s0-k+p-1)/p*p;
      for(;k<s1;k+=p) if(6*k+R!=p) __atomic_fetch_and(&P[k>>6],~(1ULL<<(k&63)),__ATOMIC_RELAXED);
    }
  }
  // clear the bits above NK
  if(NK%64) P[NW-1]&=(1ULL<<(NK%64))-1;
  PB[R]=P;
}
int main(int argc,char**argv){
  int RES=atoi(argv[1]); u64 B=strtoull(argv[2],0,10);
  NK=B/6+1; NW=(NK+63)/64;
  u64 sq=(u64)sqrt((double)B)+2; char*sm=calloc(sq+1,1);
  for(u64 i=2;i<=sq;i++) if(!sm[i]) for(u64 j=i*i;j<=sq;j+=i) sm[j]=1;
  int np=0; u64*pr=malloc(sizeof(u64)*sq); for(u64 i=5;i<=sq;i++) if(!sm[i]) pr[np++]=i;
  int Rs[2]; int nR=0; if(RES==0){Rs[0]=1;Rs[1]=5;nR=2;} else {Rs[0]=RES;nR=1;}
  for(int i=0;i<nR;i++) build(Rs[i],B,pr,np);
  fprintf(stderr,"sieve ready NK=%llu\n",(unsigned long long)NK);
  for(int ai=3; ai<argc; ai++){
    u64 K=strtoull(argv[ai],0,10);
    static u64 T[8192]; int nt=0;
    for(int x=1;x<62;x++) for(int y=1;y<62;y++){ long double s=ldexpl(1,x)+(long double)K*ldexpl(1,y); if(s<(long double)B) T[nt++]=(1ULL<<x)+K*(1ULL<<y); }
    for(int i=1;i<nt;i++){ u64 v=T[i]; int j=i-1; while(j>=0&&T[j]>v){T[j+1]=T[j];j--;} T[j+1]=v; }
    long long zeros=0;
    for(int c=1;c<=5;c+=2){
      static u64 S[16384]; static const u64* SP[16384]; int ns=0;
      for(int i=0;i<nt;i++) for(int ri=0;ri<nR;ri++){ int R=Rs[ri];
        if((int)((T[i]%6+6+R-c)%6)==0){ S[ns]=(T[i]+R-c)/6; SP[ns]=PB[R]; ns++; } }
      u64 J=(B-c)/6+1; u64 JW=(J+63)/64;
      #pragma omp parallel for schedule(dynamic,256) reduction(+:zeros)
      for(u64 w=0; w<JW; w++){
        u64 acc=0; u64 jb=w*64;
        u64 valid=(jb+64<=J)? ~0ULL : ((1ULL<<(J-jb))-1);
        for(int i=0;i<ns && acc!=valid;i++) acc|=word_at(SP[i],(int64_t)jb-(int64_t)S[i]);
        u64 miss=valid&~acc;
        while(miss){ int b=__builtin_ctzll(miss); miss&=miss-1; u64 m=6*(jb+b)+c;
          #pragma omp critical
          { printf("%llu %llu\n",(unsigned long long)K,(unsigned long long)m); }
          zeros++; }
      }
    }
    fflush(stdout);
    fprintf(stderr,"K=%llu RES=%d m<%llu zeros=%lld\n",(unsigned long long)K,RES,(unsigned long long)B,zeros);
  }
  return 0;
}
