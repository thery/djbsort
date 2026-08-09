import subprocess,sys
def clist(n):
    out=subprocess.run(['/tmp/dump2',str(n)],capture_output=True,text=True).stdout.split('\n')
    k=int(out[0].split()[1])
    pairs=[tuple(map(int,out[1+i].split())) for i in range(k)]
    perm=[int(out[2+k+i].split()[0]) for i in range(n)]
    inv=[0]*n
    for s,w in enumerate(perm): inv[w]=s
    return [(inv[a],inv[b]) for (a,b) in pairs]
def textbook(n):
    r=[];k=2
    while k<=n:
        j=k//2
        while j>0:
            for i in range(n):
                l=i^j
                if l>i:
                    r.append((i,l) if (i&k)==0 else (l,i))
            j//=2
        k*=2
    return r
c=clist(64); t=textbook(64)
print("C:",len(c)," textbook:",len(t))
print("C   first 12:",c[:12])
print("book first 12:",t[:12])
# how many agree as a set
print("same multiset:", sorted(c)==sorted(t))

def raw(n):
    out=subprocess.run(['/tmp/dump2',str(n)],capture_output=True,text=True).stdout.split('\n')
    k=int(out[0].split()[1])
    return [tuple(map(int,out[1+i].split())) for i in range(k)]
r=raw(64)
print("raw first 12:",r[:12])
def variant(n,flip):
    res=[];k=2
    while k<=n:
        j=k//2
        while j>0:
            for i in range(n):
                l=i^j
                if l>i:
                    asc=((i&k)==0)!=flip
                    res.append((i,l) if asc else (l,i))
            j//=2
        k*=2
    return res
for fl in (False,True):
    v=variant(64,fl)
    print("flip",fl,"tail match:", sorted(v[96:])==sorted(c[80:]), len(v[96:]), len(c[80:]))
