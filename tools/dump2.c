#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int32_t *ct_a,*ct_b; long long ct_n;
void int32_sort_short_ct(int32_t*,long long);
int main(int argc,char**argv){
  long long n=atoll(argv[1]);
  ct_a=malloc(40000000*4); ct_b=malloc(40000000*4);
  int32_t *x=malloc(n*4);
  for(long long i=0;i<n;i++) x[i]=(int32_t)(2*i);
  ct_n=0; int32_sort_short_ct(x,n);
  printf("P %lld\n",ct_n);
  for(long long i=0;i<ct_n;i++){
    int32_t a=ct_a[i],b=ct_b[i];
    if(a&1) printf("%d %d\n",b/2,a/2); else printf("%d %d\n",a/2,b/2);
  }
  printf("M\n");
  for(long long i=0;i<n;i++) printf("%d %d\n",x[i]/2,x[i]&1);
  return 0;
}
