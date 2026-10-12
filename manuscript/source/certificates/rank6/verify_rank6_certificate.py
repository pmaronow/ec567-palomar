#!/usr/bin/env python3
"""Finite arithmetic certificate for the rank-six family.

Uses only the Python standard library. Uniform local arguments and analytic
infinitude are proved in the manuscript; primitive quartic modular checks
verify finite local premises.
"""
from fractions import Fraction as Q
from math import gcd,isqrt,prod
from pathlib import Path
import json
FORMS=((1,0),(0,1),(169,750),(25,-169),(1,-27),(7,20),
       (2,-21),(9,10),(1,15),(7,64),(1,-2),(32,-105))
F=tuple(range(4));H=tuple(range(4,8));J=tuple(range(8,12))
CONSTS=(-1,2,3,7)
S=(2,3,5,7,11,13,17,19,23,41)


def vp(x,p):
    assert x
    k=0
    while x%p==0:x//=p;k+=1
    return k

def prime(p):return p>1 and all(p%d for d in range(2,isqrt(p)+1))

def factor(x):
    out={-1:int(x<0)};x=abs(x);assert x
    for p in S:
        k=vp(x,p);x//=p**k
        if k:out[p]=k
    assert x==1
    return out

def legendre(z,p):
    e=pow(z%p,(p-1)//2,p);assert e in (1,p-1)
    return int(e!=1)

def basis(rows):
    B={}
    for r in rows:
        while r:
            p=r.bit_length()-1
            if p in B:r^=B[p]
            else:B[p]=r;break
    return B

def nullspace(rows,width):
    B=basis(rows);out=[]
    for free in range(width):
        if free in B:continue
        v=1<<free
        for p in sorted(B):
            if (v&B[p]).bit_count()%2:v^=1<<p
        out.append(v)
    assert all((r&v).bit_count()%2==0 for r in rows for v in out)
    return out

def localcode(z,p):
    v=vp(z,p);u=z//p**v
    if p==2:return {1:0,3:5,5:4,7:1}[u%8]^(2*(v%2))
    return legendre(u,p)^(2*(v%2))

def modular_upper(a,b,p,k):
    mod=p**k;squares={w*w%mod for w in range(mod)}
    nr=next((n for n in range(2,p)if legendre(n,p)),2)
    reps=[1,-1,2,-2,5,-5,10,-10]if p==2 else[1,nr,p,nr*p]
    allowed=[]
    for d in reps:
        vd=vp(d,p)
        if vd and b%p:continue
        du=d//p**vd;bd=(b//p**vd)*pow(du,-1,mod)%mod
        if any((d*v**4+a*v*v+bd)%mod in squares for v in range(mod)) or any((d+a*u*u+bd*u**4)%mod in squares for u in range(0,mod,p)):
            allowed.append(localcode(d,p))
    return sorted(allowed)

def model(m,n):
    L=[a*m+b*n for a,b in FORMS];f,h,j=[prod(L[i]for i in g)for g in(F,H,J)]
    assert 25*f+16*h==9*j
    a,b,c=70*f,-784*f*h,1764*f*j
    assert a*a-4*b==c
    return L,(f,h,j),((a,b),(-2*a,c))

def main():
    data=json.loads(Path(__file__).with_name('rank6_certificate.json').read_text())
    m,n=data['m'],data['n'];ci=data['ci'];states={int(q):r for q,r in data['states'].items()}
    assert(m,n)==(19,11)
    assert all(prime(p)for p in S)
    assert all(gcd(a,b)==1 for a,b in FORMS)
    determinants=[]
    for i,(a,b)in enumerate(FORMS):
        if b:factor(b)
        for j,(c,d)in enumerate(FORMS[i+1:],i+1):
            det=a*d-b*c;assert det
            determinants.append(dict(i=i,j=j,value=det,factors=factor(det)))
    assert len(determinants)==66
    recorded=[dict(r,factors={int(p):e for p,e in r['factors'].items()})for r in data['determinant_factorizations']]
    assert determinants==recorded
    # Thirteen exact evaluations prove degree12 homogeneous point identities.
    for x in range(13):
        L,(f,h,j),curves=model(x,1)
        D=x*x+30;T=25*x*x-338*x-750
        sections=[[(14*h,14*h*42*D),(-2*L[1]*L[2]*L[4]*L[5],-2*L[1]*L[2]*L[4]*L[5]*3*(3*T+65*D)),(-175*L[1]*L[3]*L[4]*L[6],-175*L[1]*L[3]*L[4]*L[6]*Q(21,5)*(52*x*x+375*x-975))],[(14*f,-14*f*168*D),(2*L[0]*L[3]*L[10]*L[11],2*L[0]*L[3]*L[10]*L[11]*8*(2*T-55*D)),(Q(18,25)*L[0]*L[2]*L[8]*L[11],Q(18,25)*L[0]*L[2]*L[8]*L[11]*Q(8,5)*(39*x*x-500*x+4550))]]
        for(a,b),points in zip(curves,sections):
            for X,Y in points:assert Y*Y==X*X*X+a*X*X+b*X
        A=2*T-55*D;Q0=39*x*x-500*x+4550
        V2=L[0]*L[3]*L[10]*L[11];U2=L[1]*L[2]*L[8]*L[9]
        V3=L[0]*L[2]*L[8]*L[11];U3=L[1]*L[3]*L[9]*L[10]
        images=[(7056*D*D,294*D*(9*j-f)),(16*A*A,2*A*(V2-441*U2)),(Q(16,25)*Q0*Q0,Q(2,125)*Q0*(9*V3-30625*U3))]
        a,b=curves[0];c=curves[1][1]
        for X,Y in sections[0]+images:assert Y*Y==X*X*X+a*X*X+b*X
        for(X,Y),(u,v)in zip(sections[1],images):
            if X:
                assert Q(Y*Y,4*X*X)==u and Q(Y*(X*X-c),8*X*X)==v
    L,(f,h,j),curves=model(m,n);pi=[v//c for v,c in zip(L,ci)]
    assert all(v%c==0 for v,c in zip(L,ci))
    assert ci==[2**vp(v,2)*3**vp(v,3)for v in L]
    assert pi[0]%8==3 and pi[0]%4==3
    moduli={int(q):pair for q,pair in data['moduli'].items()};W=prod(moduli)
    residues=[sum(pair[k]*(W//q)*pow(W//q,-1,q)for q,pair in moduli.items())%W for k in (0,1)]
    assert (W,*residues)==(data['W'],data['M0'],data['N0'])==(780373440,416513683,91046603)
    assert all((residues[0]%q,residues[1]%q)==tuple(pair)for q,pair in moduli.items())
    canonical,_,_=model(*residues);quotients=[z//c for z,c in zip(canonical,ci)]
    assert all(z%c==0 for z,c in zip(canonical,ci))
    assert all(c==2**vp(z,2)*3**vp(z,3)for z,c in zip(canonical,ci))
    retained=set(data['crt_primes']);omitted=set(S)-retained
    assert retained=={2,3,5,7,11,17,23}
    assert all(gcd(p,W)==1 for p in quotients)
    for i,((a,b),c)in enumerate(zip(FORMS,ci)):
        assert W%c==0 and all((a*W//c)%q==(b*W//c)%q==0 for q in retained)
    for q in omitted:
        directions={(1,b*pow(a,-1,q)%q)if a%q else(0,1)for a,b in FORMS}
        assert len(directions)==data['omitted_direction_counts'][str(q)]<q+1
    # Check local premises at the representative pair.
    a,b=curves[0];alpha=a//16;beta=b//256
    assert vp(f,2)==3 and vp(h,2)==1 and vp(j,2)==3
    assert alpha%4==1 and beta%8==3
    assert curves[1][0]//16==-2*alpha and curves[1][1]//256==alpha*alpha-4*beta
    assert a%3==b%3==1
    assert ((a//7)%7,(b//49)%7)==(2,4)
    assert ((curves[1][0]//7)%7,(curves[1][1]//49)%7)==(3,2)
    assert all(vp(c,2)<=3 and vp(c,3)<=3 for c in ci)
    fixed={}
    fresh_local={}
    for k,side in enumerate(('E','Ep')):
        a,b=curves[k];rows=[];local=[]
        g=F+H if k==0 else F+J
        columns=CONSTS+tuple(pi[i]for i in g)
        for p,precision in((2,9),(3,5),(7,3)):
            aa,bb=a,b;scale=0
            while aa%p**2==0 and bb%p**4==0:aa//=p**2;bb//=p**4;scale+=1
            allowed=modular_upper(aa,bb,p,precision)
            expected=data['fixed_local'][side][len(local)]
            assert scale==expected['scale']
            assert len(basis(allowed+expected['allowed_codes']))==len(basis(allowed))==len(basis(expected['allowed_codes']))
            coords=[localcode(z,p)for z in columns]
            for ann in nullspace(allowed,3 if p==2 else 2):
                row=sum(((ann&c).bit_count()%2)<<i for i,c in enumerate(coords))
                if row:rows.append(row)
            local.append(dict(p=p,precision=precision,scale=scale,allowed_codes=allowed))
        if k:rows.append(1)
        assert rows==data['fixed_rows'][side]
        fixed[side]=rows;fresh_local[side]=local
    chars=[]
    for i,((a,b),c)in enumerate(zip(FORMS,ci)):
        ch={-1:int(quotients[i]%4==3),2:int(quotients[i]%8 in(3,5))}
        for q in S:
            if q==2:continue
            residue=quotients[i]if q in retained else(a*states[q][0]+b*states[q][1])*pow(c,-1,q)
            ch[q]=legendre(residue,q)^(((q-1)//2%2)&ch[-1])
        chars.append(ch)
    def symbol(z,i,characters=chars):
        return sum((e%2)*characters[i][p]for p,e in factor(z).items())%2
    def crossings(characters):
        cross=[[0]*12 for _ in range(12)]
        for i,(ai,bi)in enumerate(FORMS):
            for j,(aj,bj)in enumerate(FORMS):
                if i==j:continue
                if i==0:cross[i][j]=symbol(bj*ci[j],0,characters)
                else:
                    cross[i][j]=symbol(bi*ci[i],0,characters)^(characters[0][-1]&characters[i][-1])
                    if j:cross[i][j]^=symbol(ci[0]*ci[j]*(bi*aj-bj*ai)*bi,i,characters)
        return cross
    cross=crossings(chars)
    assert all(cross[i][j]^cross[j][i]==chars[i][-1]&chars[j][-1]for i in range(12)for j in range(i+1,12))
    def rows_for(side,eps,characters):
        cross=crossings(characters);g=F+H if side=='E'else F+J;opp=J if side=='E'else H
        coef=(-784 if side=='E'else 1764)*prod(ci[i]for i in g)
        rows=fixed[side][:]
        for i in F:
            row=sum(symbol(d,i,characters)<<k for k,d in enumerate(CONSTS));diagonal=symbol(coef,i,characters)
            for j in g:
                if j!=i:
                    bit=cross[i][j]^eps;diagonal^=bit;row|=bit<<(4+g.index(j))
            row|=diagonal<<(4+g.index(i));rows.append(row)
        for i in opp:
            rows.append(sum(symbol(d,i,characters)<<k for k,d in enumerate(CONSTS))|sum((cross[i][j]^eps)<<(4+g.index(j))for j in g))
        return rows
    for q in omitted:
        for i in range(12):
            changed=[dict(c)for c in chars];changed[i][q]^=1
            for side in ('E','Ep'):
                for eps in (0,1):assert rows_for(side,eps,changed)==rows_for(side,eps,chars)
    known_classes={'E':[(-784,F+H),(14,H),(-2,(1,2,4,5)),(-175,(1,3,4,6))],'Ep':[(1764,F+J),(14,F),(2,(0,3,10,11)),(Q(18,25),(0,2,8,11))]}
    known={}
    for side in('E','Ep'):
        g=F+H if side=='E'else F+J;codes=[]
        for scalar,support in known_classes[side]:
            # Clearing a constant square denominator does not change class.
            scalar=Q(scalar)*prod(ci[i]for i in support)
            scalar*=scalar.denominator**2
            fac=factor(int(scalar));assert all(p in CONSTS for p,e in fac.items()if e%2)
            code=sum((fac.get(p,0)%2)<<i for i,p in enumerate(CONSTS))|sum(1<<(4+g.index(i))for i in support)
            codes.append(code)
        assert codes==data['known_codes'][side]and len(basis(codes))==4
        known[side]=codes
    matrices={};rrefs={}
    for side in('E','Ep'):
        for eps in(0,1):
            rows=rows_for(side,eps,chars)
            label=side+str(eps);assert rows==data['matrices'][label]
            assert len(basis(rows))==8 and len(nullspace(rows,12))==4
            assert all((r&v).bit_count()%2==0 for r in rows for v in known[side])
            assert len(basis(nullspace(rows,12)+known[side]))==4
            B=basis(rows)
            for pivot in sorted(B):
                for other in B:
                    if other!=pivot and B[other]&(1<<pivot):B[other]^=B[pivot]
            matrices[label]=rows;rrefs[label]=[B[k]for k in sorted(B,reverse=True)]
            print(label,'rank8, kernel4, exactknownbasis; RREF',rrefs[label])
    result=dict(anchor=[m,n],cofactors=ci,determinants=determinants,fixed_local=fresh_local,known=known,matrices=matrices,rrefs=rrefs,status='PASS independent arithmetic; local uniformity and analytic infinity are separate mathematical inputs')
    assert rrefs['E0']==rrefs['E1']==[2137,1048,521,328,209,33,4,2]
    assert rrefs['Ep0']==rrefs['Ep1']==[2072,1068,552,284,164,84,2,1]
    print('PASS all six section identities, six points on E and dual map; reduced CRT; 36 zero character derivatives; 66 factored determinants; p0=3 mod 4 reciprocity signs; four sharp matrices.')

if __name__=='__main__':main()
