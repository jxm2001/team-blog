NTT
===

说明
---

1. 使用前只需要初始化 $\text{init}$ 函数

2. 代码中的参数 $n$ 表示 $\bmod x^n$
3. 传入数组需要开 $4$ 倍空间，只需要保证前 $n$ 位正确性即可，高位不需要清零
4. $\text{ln}$  函数需要保证 $a_0=1$，$\text{exp}$ 函数需要保证 $a_0=0$

5. 一般情况下 $\text{pow}$  函数中 $k_1=k_2=k$ 即可，高精度幂次下 $k_1\equiv k\bmod p,k_2\equiv k\bmod (p-1)$,同时要特判 $f(x)^k\equiv 0\bmod x^n$ 的情况，具体代码如下

```cpp
int k1=0,k2=0;
_for(i,0,n)a[i]=read_int();
for(int i=0,len=strlen(buf);i<len;i++){
    k1=(10LL*k1+buf[i]-'0')%Mod;
    k2=(10LL*k2+buf[i]-'0')%(Mod-1);
    if(!a[0]&&k1>=n){
        _for(i,0,n)a[i]=0;
        break;
    }
}
Poly::Pow(a,b,n,k1,k2);
```

6. $\text{sqrt}$ 函数需要和以下代码配套

```cpp
template <typename T1,typename T2>
struct HASH_Table{
	static const int HASH_MOD=3000017,MAXS=5e6;
	struct cell{
		T1 key;T2 val;
		int next;
	}e[MAXS];
	int head[HASH_MOD],cnt;
	void clear(){mem(head,0);cnt=0;}
	T2 insert(T1 Key,T2 Value){
		int h=Key%HASH_MOD;
		e[++cnt].key=Key,e[cnt].val=Value,e[cnt].next=head[h];
		head[h]=cnt;
		return Value;
	}
	T2 find(T1 Key){
		int h=Key%HASH_MOD;
		for(int i=head[h];i;i=e[i].next){
			if(e[i].key==Key)
			return e[i].val;
		}
		return -1;
	}
};
HASH_Table<int,int> H;
int bsgs(int a,int b){
	H.clear();
	int m=sqrt(Mod)+1,t=b,base;
	for(int i=1;i<=m;i++){
		t=1LL*t*a%Mod;
		H.insert(t,i);
	}
	t=1,base=quick_pow(a,m);
	for(int i=1;i<=m;i++){
		t=1LL*t*base%Mod;
		if(H.find(t)!=-1)return m*i-H.find(t);
	}
	return -1;
}
```

模板
---

```cpp
const int Mod=998244353;
int quick_pow(int a,int b){
	int ans=1;
	while(b){
		if(b&1)
		ans=1LL*ans*a%Mod;
		a=1LL*a*a%Mod;
		b>>=1;
	}
	return ans;
}
namespace Poly{
	const int G=3;
	int rev[MAXN<<2],Pool[MAXN<<3],*Wn[30];
	void init(){
		int lg2=0,*pos=Pool,n,w;
		while((1<<lg2)<MAXN*2)lg2++;
		n=1<<lg2,w=quick_pow(G,(Mod-1)/(1<<lg2));
		while(~lg2){
			Wn[lg2]=pos,pos+=n;
			Wn[lg2][0]=1;
			_for(i,1,n)Wn[lg2][i]=1LL*Wn[lg2][i-1]*w%Mod;
			w=1LL*w*w%Mod;
			lg2--;n>>=1;
		}
	}
	int build(int k){
		int n,pos=0;
		while((1<<pos)<=k)pos++;
		n=1<<pos;
		_for(i,0,n)rev[i]=(rev[i>>1]>>1)|((i&1)<<(pos-1));
		return n;
	}
	void NTT(int *f,int n,bool type){
		_for(i,0,n)if(i<rev[i])
		swap(f[i],f[rev[i]]);
		int t1,t2;
		for(int i=1,lg2=1;i<n;i<<=1,lg2++){
			for(int j=0;j<n;j+=(i<<1)){
				_for(k,j,j+i){
					t1=f[k],t2=1LL*Wn[lg2][k-j]*f[k+i]%Mod;
					f[k]=(t1+t2)%Mod,f[k+i]=(t1-t2)%Mod;
				}
			}
		}
		if(!type){
			reverse(f+1,f+n);
			int div=quick_pow(n,Mod-2);
			_for(i,0,n)f[i]=(1LL*f[i]*div%Mod+Mod)%Mod;
		}
	}
	void Mul(int *f,int _n,int *g,int _m,int xmod=0){
		int n=build(_n+_m-2);
		_for(i,_n,n)f[i]=0;_for(i,_m,n)g[i]=0;
		NTT(f,n,true);NTT(g,n,true);
		_for(i,0,n)f[i]=1LL*f[i]*g[i]%Mod;
		NTT(f,n,false);
		if(xmod)_for(i,xmod,n)f[i]=0;
	}
	void Inv(const int *f,int *g,int _n){
		static int temp[MAXN<<2];
		if(_n==1)return g[0]=quick_pow(f[0],Mod-2),void();
		Inv(f,g,(_n+1)>>1);
		int n=build((_n-1)<<1);
		_for(i,(_n+1)>>1,n)g[i]=0;
		_for(i,0,_n)temp[i]=f[i];_for(i,_n,n)temp[i]=0;
		NTT(g,n,true);NTT(temp,n,true);
		_for(i,0,n)g[i]=(2-1LL*temp[i]*g[i]%Mod)*g[i]%Mod;
		NTT(g,n,false);
		_for(i,_n,n)g[i]=0;
	}
	void Div(const int *f,int _n,const int *g,int _m,int *q,int *r){
		static int temp[MAXN<<2];
		if(_n<_m){
			_rep(i,0,n)r[i]=f[i];
			return;
		}
		_rep(i,0,_m)temp[i]=g[_m-i];
		Inv(temp,q,_n-_m+1);
		_rep(i,0,_n)temp[i]=f[_n-i];
		Mul(q,_n-_m+1,temp,_n+1,_n-_m+1);
		for(int i=0,j=_n-_m;i<j;i++,j--)swap(q[i],q[j]);
		int __m=min(_n-_m+1,_m);
		_for(i,0,_m)r[i]=g[i];_for(i,0,__m)temp[i]=q[i];
		Mul(r,_m,temp,__m,_m);
		_for(i,0,_m)r[i]=(f[i]+Mod-r[i])%Mod;
	}
	void Ln(const int *f,int *g,int _n){
		static int temp[MAXN<<2];
		Inv(f,g,_n);
		_for(i,1,_n)temp[i-1]=1LL*f[i]*i%Mod;
		temp[_n-1]=0;
		Mul(g,_n,temp,_n-1,_n);
		for(int i=_n-1;i;i--)g[i]=1LL*g[i-1]*quick_pow(i,Mod-2)%Mod;
		g[0]=0;
	}
	void Exp(const int *f,int *g,int _n){
		static int temp[MAXN<<2];
		if(_n==1)return g[0]=1,void();
		Exp(f,g,(_n+1)>>1);
		_for(i,(_n+1)>>1,_n)g[i]=0;
		Ln(g,temp,_n);
		temp[0]=(1+f[0]-temp[0])%Mod;
		_for(i,1,_n)temp[i]=(f[i]-temp[i])%Mod;
		Mul(g,(_n+1)>>1,temp,_n,_n);
	}
	void Pow(const int *f,int *g,int _n,int k1,int k2){
		static int temp[MAXN<<2];
		int pos=0,posv;
		while(!f[pos]&&pos<_n)pos++;
		if(1LL*pos*k2>=_n){
			_for(i,0,_n)g[i]=0;
			return;
		}
		posv=quick_pow(f[pos],Mod-2);
		_for(i,pos,_n)g[i-pos]=1LL*f[i]*posv%Mod;
		_for(i,_n-pos,_n)g[i]=0;
		Ln(g,temp,_n);
		_for(i,0,_n)temp[i]=1LL*temp[i]*k1%Mod;
		Exp(temp,g,_n);
		pos=pos*k2,posv=quick_pow(posv,1LL*k2*(Mod-2)%(Mod-1));
		for(int i=_n-1;i>=pos;i--)g[i]=1LL*g[i-pos]*posv%Mod;
		_for(i,0,pos)g[i]=0;
	}
	void Sqrt(const int *f,int *g,int _n){
		static int temp1[MAXN<<2],temp2[MAXN<<2];
		if(_n==1)return g[0]=quick_pow(G,bsgs(3,f[0])/2),void();
		Sqrt(f,g,(_n+1)>>1);
		_for(i,(_n+1)>>1,_n)g[i]=0;
		_for(i,0,_n)temp1[i]=f[i];
		Inv(g,temp2,_n);
		Mul(temp1,_n,temp2,_n);
		int div2=quick_pow(2,Mod-2);
		_for(i,0,_n)g[i]=1LL*(g[i]+temp1[i])*div2%Mod;
	}
}
```

