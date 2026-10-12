#!/usr/bin/env python3
"""Finite arithmetic certificate for the rank-seven family.

Run from source/: python3 -I certificates/rank7/verify_rank7_certificate.py
Uses only the Python standard library. Mathematical infinitude and the uniform
valuation arguments are proved in the manuscript.
"""
from fractions import Fraction as Q
from math import gcd, isqrt, prod
from pathlib import Path
import json

FORMS = ((1,0),(0,1),(1,-182),(182,10557),(9,34),(25,-4968),
         (2,-5589),(8,425),(13,2688),(325,49266),(14,-975),(896,-45747))
CI = (18,1,64,9,8,18,9,1,6,1728,3,9)
CONSTANTS = (-1,2,3,7,13)
ACTIVE = (2,3,7,11,13,17,19,23)
SUPPORT = (2,3,5,7,11,13,17,19,23,29,37,41,47,59,61,109,241,409)
F, H, J = tuple(range(4)), tuple(range(4,8)), tuple(range(8,12))

class Poly:
    """Exact univariate rational coefficients, low degree first."""
    def __init__(self, co):
        if isinstance(co, Poly): co = co.c
        elif isinstance(co, (int,Q)): co = [co]
        self.c = [Q(x) for x in co]
        while len(self.c)>1 and not self.c[-1]: self.c.pop()
    def __add__(self,b):
        b=Poly(b)
        return Poly([(self.c[i] if i<len(self.c) else 0)+
                     (b.c[i] if i<len(b.c) else 0)
                     for i in range(max(len(self.c),len(b.c)))])
    __radd__=__add__
    def __neg__(self): return Poly([-x for x in self.c])
    def __sub__(self,b): return self+-Poly(b)
    def __rsub__(self,b): return Poly(b)+-self
    def __mul__(self,b):
        b=Poly(b); out=[Q(0)]*(len(self.c)+len(b.c)-1)
        for i,x in enumerate(self.c):
            for j,y in enumerate(b.c): out[i+j]+=x*y
        return Poly(out)
    __rmul__=__mul__
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        out=Poly(1)
        for _ in range(n): out*=self
        return out
    def __truediv__(self,b):
        b=Poly(b); assert b.c != [0]
        if len(b.c)==1: return Poly([x/b.c[0] for x in self.c])
        rem=self.c[:]; out=[Q(0)]*max(1,len(rem)-len(b.c)+1)
        while len(rem)>=len(b.c) and rem != [0]:
            k=len(rem)-len(b.c); q=rem[-1]/b.c[-1]; out[k]=q
            for i,x in enumerate(b.c): rem[i+k]-=q*x
            while len(rem)>1 and not rem[-1]: rem.pop()
        assert rem==[0], (self.c,b.c,rem)
        return Poly(out)
    def __eq__(self,b): return self.c==Poly(b).c

def prime(p): return p>1 and all(p%d for d in range(2,isqrt(p)+1))
def factor(z):
    assert z; out={-1:int(z<0)}; z=abs(z)
    for p in SUPPORT:
        e=0
        while z%p==0: z//=p; e+=1
        if e: out[p]=e
    assert z==1, (z,out)
    return out
def vp(z,p):
    assert z; e=0
    while z%p==0: z//=p; e+=1
    return e
def leg(z,p):
    r=pow(z%p,(p-1)//2,p); assert r in (1,p-1)
    return int(r!=1)
def code(z,p):
    e=vp(z,p); u=z//p**e
    if p==2: return {1:0,3:5,5:4,7:1}[u%8] ^ (2 if e%2 else 0)
    return leg(u,p) ^ (2 if e%2 else 0)
def basis(rows):
    out={}
    for z in rows:
        while z:
            p=z.bit_length()-1
            if p in out: z^=out[p]
            else: out[p]=z; break
    return out
def rref(rows):
    out=basis(rows)
    for p in sorted(out):
        for q in out:
            if p!=q and out[q]&(1<<p): out[q]^=out[p]
    return [out[p] for p in sorted(out,reverse=True)]
def kernel(rows,width):
    out=[]; b=basis(rows)
    for free in range(width):
        if free in b: continue
        z=1<<free
        for p in sorted(b):
            if (z&b[p]).bit_count()%2: z^=1<<p
        out.append(z)
    assert all((z&r).bit_count()%2==0 for z in out for r in rows)
    return out
def annihilator(rows,width):
    return list(basis(z for z in range(1<<width)
                      if all((z&r).bit_count()%2==0 for r in rows)).values())

def main():
    here=Path(__file__).resolve().parent
    data=json.loads((here/'rank7_certificate.json').read_text())
    assert tuple(map(tuple,data['forms']))==FORMS
    assert tuple(data['cofactors'])==CI
    assert all(prime(p) for p in SUPPORT)
    assert all(gcd(a,b)==1 for a,b in FORMS)

    # N=1 preserves a homogeneous polynomial identity. All displayed L have
    # degree1, quadratics degree2, point x degree4 and y degree6; every point
    # residual is homogeneous degree12, so exact coefficients here suffice.
    m=Poly([0,1]); ls=[Poly([b,a]) for a,b in FORMS]
    def product(xs):
        z=Poly(1)
        for x in xs: z*=x
        return z
    f,h,j=[product(ls[i] for i in g) for g in (F,H,J)]
    a,b,c=91205*f,-33124*f*h,9*f*j
    assert a*a-4*b==c
    d=m*m+10557; t=m*m-364*m-10557
    z=-182*m*m-21114*m+1921374
    assert z*z+10557*t*t==43681*d*d
    a1=175*m*m+10738*m+2470338
    a2=364*m*m+36639*m-2825550
    a3=728*m*m-592647*m+28820610
    b1=49*m*m-43862*m-2026944
    b2=2912*m*m+2544237*m-432309150
    actual={'E':[(-1,F+H),(-1,F),(1,(0,2,6,7)),
                 (-91,(1,2,5,6)),(182,(2,3,6,7))],
            'Ep':[(1,F+J),(1,F),(1,(0,2,8,9)),(1,(0,3,8,10))]}
    points={'E':[(-58081*f,Q(10920,241)*d),
                  (Q(1225,9)*product(ls[i] for i in (0,2,6,7)),Q(4,15)*a1),
                  (-2275*product(ls[i] for i in (1,2,5,6)),-Q(6,5)*a2),
                  (Q(182,361)*product(ls[i] for i in (2,3,6,7)),a3/19)],
            'Ep':[(3481*f,Q(21840,59)*d),
                  (Q(49,64)*product(ls[i] for i in (0,2,8,9)),Q(65,56)*b1),
                  (Q(16,225)*product(ls[i] for i in (0,3,8,10)),b2/60)]}
    # Link each claimed actual class to its torsion coefficient or literal
    # point coordinate, rather than merely checking a separate support table.
    for side,tor in [('E',b),('Ep',c)]:
        xs=[tor]+[x for x,r in points[side]]
        for x,(scalar,supp) in zip(xs,actual[side]):
            q=x/(scalar*product(ls[i] for i in supp))
            assert len(q.c)==1 and q.c[0]>0
            qq=q.c[0]
            assert isqrt(qq.numerator)**2==qq.numerator
            assert isqrt(qq.denominator)**2==qq.denominator
    for side,aa,bb in [('E',a,b),('Ep',-2*a,c)]:
        for x,r in points[side]: assert (x*r)**2==x**3+aa*x*x+bb*x
    for x,r in points['Ep']:
        xx=r*r/4; yy=r*(x-c/x)/8
        assert yy*yy==xx**3+a*xx*xx+b*xx
    x7=8281*t*t; y7=Q(8281,2)*d*t*z
    assert y7*y7==x7**3+a*x7*x7+b*x7

    # CRT, affine content, output unit residues and local constancy precision.
    states={int(s['modulus']):(int(s['M']),int(s['N'])) for s in data['states']}
    w=prod(states)
    def crt(k):
        return sum(v[k]*(w//q)*pow(w//q,-1,q) for q,v in states.items())%w
    m0,n0=crt(0),crt(1)
    assert (w,m0,n0)==(308403583488,79151095314,151444919819)
    assert data['lattice']==dict(W=w,M0=m0,N0=n0)
    assert all(gcd(q,r)==1 for q in states for r in states if q!=r)
    vals=[aa*18+bb*11 for aa,bb in FORMS]
    pi=[v//cc for v,cc in zip(vals,CI)]
    assert all(v%cc==0 for v,cc in zip(vals,CI))
    assert [2**vp(v,2)*3**vp(v,3) for v in vals]==list(CI)
    assert all(9-vp(cc,2)>=3 and 4-vp(cc,3)>=1 for cc in CI)
    aff=[]; residues={}
    for (aa,bb),cc in zip(FORMS,CI):
        assert w%cc==0 and (aa*m0+bb*n0)%cc==0
        q=(aa*w//cc,bb*w//cc,(aa*m0+bb*n0)//cc)
        assert gcd(gcd(q[0],q[1]),q[2])==1
        assert all(q[0]%p==q[1]%p==0 and q[2]%p for p in ACTIVE)
        assert q[0]%8==q[1]%8==0 and q[2]%8==pi[len(aff)]%8
        assert q[2]%3==pi[len(aff)]%3
        aff.append(q)
    admissible={}
    for p in (2,3,5,7,11):
        good=[(u,v) for u in range(p) for v in range(p)
              if all((aa*u+bb*v+cc)%p for aa,bb,cc in aff)]
        assert good; admissible[p]=dict(count=len(good),witness=good[0])
    assert all(aa*3000+bb>0 for aa,bb in FORMS)
    fv,hv,jv=[prod(vals[i] for i in g) for g in (F,H,J)]
    assert (vp(fv,2),vp(hv,2),vp(jv,2))==(7,4,7)
    assert (91205*fv//64)%16==10
    assert (-33124*fv*hv//4096)%16==14
    assert (vp(fv,3),vp(hv,3),vp(jv,3))==(4,4,7)
    assert (91205*fv//81)%3==(-33124*fv*hv//6561)%3==1
    assert [u for u in (1,3,5,7) if u*(u*u+2*u+6)%8==1]==[1]
    assert [u for u in (1,3,5,7) if u*(2*u*u+2*u+7)%8==1]==[7]
    assert {code(s*s+2*r*r,2) for s in range(16) for r in range(16)
            if s%2 or r%2}=={0,2,5,7}
    for p in (7,13):
        mm,nn=states[p]; vv=[aa*mm+bb*nn for aa,bb in FORMS]
        ff,hh,jj=[prod(vv[i] for i in g) for g in (F,H,J)]
        aa,bb,cc=91205*ff,-33124*ff*hh,9*ff*jj
        assert all(v%p for v in vv)
        assert bb%p==0 and cc%p==aa*aa%p and leg(aa,p)==0

    # Fresh fixed rows, from the proved local-image coordinate bounds only.
    fixed={}
    local_bounds={'E':{2:[3],3:[],7:[1,2],13:[1,2]},
                  'Ep':{2:[2,5],3:[1,2],7:[],13:[]}}
    for side in ('E','Ep'):
        group=F+H if side=='E' else F+J
        columns=list(CONSTANTS)+[pi[i] for i in group]; rows=[]
        for p in (2,3,7,13):
            coords=[code(v,p) for v in columns]
            for mask in annihilator(local_bounds[side][p],3 if p==2 else 2):
                row=sum(((mask&z).bit_count()%2)<<k for k,z in enumerate(coords))
                if row: rows.append(row)
        if side=='Ep': rows.append(1)
        assert rows==data['fixed_rows'][side]
        fixed[side]=rows

    # Every determinant is nonzero and exactly factored. Only 54 edges
    # (not H-H or J-J) occur in rows. Their nonsquare constant support, and
    # that of all nonzero b_i, is ACTIVE. Thus the ten omitted prime
    # characters cannot affect any row, singly or jointly.
    dets=[]
    for i,(aa,bb) in enumerate(FORMS):
        if bb: assert all(p in ACTIVE for p,e in factor(bb).items() if p!=-1 and e%2)
        for k,(cc,dd) in enumerate(FORMS[i+1:],i+1):
            det=aa*dd-bb*cc; assert det
            fac=factor(det)
            used=not ((i in H and k in H) or (i in J and k in J))
            if used: assert all(p in ACTIVE for p,e in fac.items() if p!=-1 and e%2)
            dets.append(dict(i=i,j=k,determinant=det,factors=fac,used=used))
    assert len(dets)==66 and sum(d['used'] for d in dets)==54
    # Give omitted characters any admissible reference values solely to
    # check all 66 reciprocity pairs, including the twelve unused edges.
    qstates={p:states[p] for p in ACTIVE if p!=2 and p!=3}
    for p in SUPPORT:
        if p not in ACTIVE:
            mm=next(mm for mm in range(p) if all((aa*mm+bb)%p for aa,bb in FORMS))
            qstates[p]=(mm,1)
    chars=[]
    for i,((aa,bb),cc) in enumerate(zip(FORMS,CI)):
        ch={-1:int(pi[i]%4==3),2:int(pi[i]%8 in (3,5))}
        for p in SUPPORT[1:]:
            rr=pi[i] if p==3 else (aa*qstates[p][0]+bb*qstates[p][1])*pow(cc,-1,p)
            ch[p]=leg(rr,p)^(((p-1)//2%2)&ch[-1])
        chars.append(ch)
    def symbol(z,i):
        return sum((e%2)*chars[i].get(p,0) for p,e in factor(z).items())%2
    cross=[[0]*12 for _ in range(12)]
    for i,(ai,bi) in enumerate(FORMS):
        for k,(ak,bk) in enumerate(FORMS):
            if i==k: continue
            if i==0: cross[i][k]=symbol(bk*CI[k],0)
            else:
                cross[i][k]=symbol(bi*CI[i],0)^(chars[0][-1]&chars[i][-1])
                if k: cross[i][k]^=symbol(CI[0]*CI[k]*(bi*ak-bk*ai)*bi,i)
    assert all(cross[i][k]^cross[k][i]==(chars[i][-1]&chars[k][-1])
               for i in range(12) for k in range(i+1,12))
    assert chars[0][-1]==0 and pi[0]%8==1

    known={}; matrices={}; refs={}
    for side in ('E','Ep'):
        group=F+H if side=='E' else F+J
        opp=J if side=='E' else H; ks=[]
        for scalar,supp in actual[side]:
            fac=factor(scalar*prod(CI[k] for k in supp))
            assert all(p in CONSTANTS for p,e in fac.items() if e%2)
            ks.append(sum((fac.get(p,0)%2)<<i for i,p in enumerate(CONSTANTS))|
                      sum(1<<(5+group.index(k)) for k in supp))
        assert ks==data['known_codes'][side]
        dim=5 if side=='E' else 4
        assert len(basis(ks))==len(basis(v>>5 for v in ks))==dim
        known[side]=ks
        coef=(-33124 if side=='E' else 9)*prod(CI[k] for k in group)
        assert all(p in ACTIVE for p,e in factor(coef).items() if p!=-1 and e%2)
        for eps in (0,1):
            rows=fixed[side][:]
            for i in F:
                row=sum(symbol(z,i)<<k for k,z in enumerate(CONSTANTS)); diag=symbol(coef,i)
                for k in group:
                    if k==i: continue
                    bit=cross[i][k]^eps; diag^=bit; row|=bit<<(5+group.index(k))
                row|=diag<<(5+group.index(i)); rows.append(row)
            for i in opp:
                rows.append(sum(symbol(z,i)<<k for k,z in enumerate(CONSTANTS))|
                            sum((cross[i][k]^eps)<<(5+group.index(k)) for k in group))
            name=side+str(eps); assert rows==data['matrices'][name]
            ref=rref(rows); assert ref==data['rrefs'][side]
            assert len(ref)==13-dim and len(kernel(rows,13))==dim
            assert all((r&v).bit_count()%2==0 for r in rows for v in ks)
            assert len(basis(kernel(rows,13)+ks))==dim
            matrices[name]=rows; refs[name]=ref
            print(name,'rank',13-dim,'kernel',dim,'RREF',ref)
    report=dict(status='PASS integrated finite arithmetic certificate',
                W=w,M0=m0,N0=n0,point_identities=7,dual_image_identities=3,
                exact_polynomial_coefficients=True,cofactors=CI,
                determinants=dets,affine_admissibility_small_primes=admissible,
                fixed_rows=fixed,known_codes=known,matrices=matrices,rrefs=refs,
                required_cross_edges=54,omitted_characters_jointly_irrelevant=True,
                rank_lower=7,rank_upper=7,
                mathematical_inputs=['Mordell-Weil and rational isogeny index formula',
                                     'uniform valuation arguments in manuscript',
                                     'published finite-complexity prime-pattern theorem'])
    (here/'rank7_certificate_output.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: exact points, CRT, local premises, factor support, all reciprocity signs, and sharp 5/4 matrices.')

if __name__=='__main__': main()
