import subprocess,sys
n=int(sys.argv[1])
out=subprocess.run(['/tmp/dump3',str(n)],capture_output=True,text=True).stdout.split('\n')
k,mn=map(int,out[0].split()[1:])
marks=[]
for i in range(mn):
    f=out[1+i].split(); marks.append((int(f[1])," ".join(f[2:])))
base=1+mn
pairs=[tuple(map(int,out[base+i].split())) for i in range(k)]
perm=[int(out[base+k+1+i]) for i in range(n)]
inv=[0]*n
for slot,w in enumerate(perm): inv[w]=slot
rel=[(inv[a],inv[b]) for (a,b) in pairs]
# batches of 8
bs=[rel[i:i+8] for i in range(0,k,8)]
bstart=[i*8 for i in range(len(bs))]
mp={}
for (idx,name) in marks: mp.setdefault(idx,[]).append(name)
print("n=%d : %d comparators = %d batches of 8\n"%(n,k,len(bs)))
for bi,b in enumerate(bs):
    o=bi*8
    for nm in mp.get(o,[]): print("--- %s"%nm)
    d=sorted(set(abs(y-x) for (x,y) in b))
    down=sum(1 for (x,y) in b if x>y)
    lo=sorted(min(x,y) for (x,y) in b)
    print("  batch %2d  distance %-12s  %d/8 reversed   min-side %s"
          %(bi, ",".join(map(str,d)), down, lo))
