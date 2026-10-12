"""Read-only independent transcription comparison. Never imports archive code."""
from pathlib import Path
import argparse, re, json, hashlib, sys, platform
import sympy as sp
from sympy.parsing.sympy_parser import parse_expr, standard_transformations, implicit_multiplication_application, convert_xor

parser = argparse.ArgumentParser(
    description="Replay 1,176 read-only mathematical transcription checks. No archive code is imported or executed.")
parser.add_argument("--updated-dir", type=Path, required=True,
                    help="Extracted updated manuscript root (containing source/sections), or its source directory.")
parser.add_argument("--original-dir", type=Path, required=True,
                    help="Extracted original rank-5 archive root (containing research), or its research directory.")
parser.add_argument("--lean-root", type=Path, required=True,
                    help="Lean repository root containing RankCertificates/*.lean.")
parser.add_argument("--output", type=Path, required=True,
                    help="Destination JSON comparison receipt; this is the only file written.")
args = parser.parse_args()

def select_root(root, suffix, marker):
    root = root.resolve()
    direct = [root / suffix, root] if suffix else [root]
    found = [p for p in direct if (p / marker).is_file()]
    if not found and root.is_dir():
        found = [p / suffix for p in sorted(root.iterdir())
                 if p.is_dir() and (p / suffix / marker).is_file()]
    if len(found) != 1:
        parser.error(f"Expected exactly one input layout for {root}; candidates: {found}")
    return found[0]

NEW = select_root(args.updated_dir, "source", "sections/06-rank5.tex")
OLD = select_root(args.original_dir, "research", "paper/final_rank5.tex")
LEAN = select_root(args.lean_root, "RankCertificates", "Rank5.lean")
OUTPUT = args.output.resolve()
EXPECTED_CHECK_COUNT = 1176
M,N=sp.symbols('M N')
TRANS=standard_transformations+(convert_xor,implicit_multiplication_application)
checks=[]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def arithmetic_parse(text, symbols=None, implicit=False):
    """Parse only integer/rational polynomial arithmetic, never supplied code.

    Validation happens before SymPy's parser. Quotes, attributes, subscripts,
    underscores, backslashes, assignment, and names other than the explicitly
    supplied mathematical symbols are rejected. The parser globals contain
    only constructors needed by SymPy's arithmetic token transformations.
    """
    symbols = {} if symbols is None else symbols
    if not isinstance(text, str) or not text.strip():
        raise ValueError("Expected a nonempty arithmetic expression")
    if re.fullmatch(r"[0-9A-Za-z\s+\-*/^(),]+", text, re.ASCII) is None:
        raise ValueError("Rejected non-arithmetic characters in expression")
    names = set(re.findall(r"[A-Za-z][A-Za-z0-9]*", text, re.ASCII))
    if not names <= symbols.keys():
        raise ValueError(f"Rejected unexpected mathematical names: {sorted(names - symbols.keys())}")
    transformations = TRANS if implicit else standard_transformations+(convert_xor,)
    return parse_expr(text, local_dict=symbols,
                      global_dict={"Integer":sp.Integer,"Rational":sp.Rational,
                                   "Float":sp.Float,"Symbol":sp.Symbol},
                      transformations=transformations)

def check(r,kind,actual,expected,ref,detail=None):
    good=actual==expected
    row={'rank':r,'category':kind,'reference':ref,'match':bool(good)}
    if detail: row['detail']=detail
    if not good: row.update(actual=str(actual),expected=str(expected))
    checks.append(row)

def tables(s):
    out={}
    for m in re.finditer(r'\\begin\{table\}.*?\\end\{table\}',s,re.S):
        labs=re.findall(r'\\label\{([^}]+)\}',m.group())
        if not labs: continue
        rows=[]
        for line in m.group().splitlines():
            if '&' not in line or not re.search(r'\\\\\s*$',line): continue
            line=line[:line.rfind('\\\\')]
            rows.append([c.strip().replace('$','') for c in line.split('&')])
        out[labs[0]]={'line':s[:m.start()].count('\n')+1,'rows':rows,'source':m.group()}
    return out

def numeric(s):
    s=s.replace('$','').replace(r'\cdot','*').replace('{','(').replace('}',')').replace('^','**')
    return int(arithmetic_parse(s))

def tex(s,env):
    s=s.replace('$','')
    s=re.sub(r'\\(?:tfrac|frac)\s*(\{[^{}]+\}|\d)\s*(\{[^{}]+\}|\d)',lambda m:'(('+m[1].strip('{}')+')/('+m[2].strip('{}')+'))',s)
    s=re.sub(r'L_\{([0-9,]+)\}',lambda m:'*'.join('L'+i for i in m[1].split(',')),s)
    s=re.sub(r'([LDV])_(\d)',r'\1\2',s)
    s=s.replace(r'\Big','').replace(r'\big','').replace(r'\left','').replace(r'\right','')
    s=s.replace(r'\cdot','*').replace(r'\,',' ').replace(r'\ ',' ').replace(r'\qquad',' ').replace(r'\quad',' ')
    s=s.replace('{','(').replace('}',')')
    # All named polynomials are expanded before using only M and N as symbols.
    pat='|'.join(sorted(map(re.escape,env),key=len,reverse=True))
    s=re.sub('('+pat+')',lambda m:'('+str(env[m[0]])+')',s)
    s=s.replace('MN','M*N')
    symbols=set().union(*(e.free_symbols for e in env.values()))
    return sp.expand(arithmetic_parse(s,{'M':M,'N':N,**{str(z):z for z in symbols}},implicit=True))

def lean_defs(s):
    out={}
    for m in re.finditer(r'^def ([A-Za-z0-9\'α]+) [^\n]*?:=\s*(.*?)(?=\n(?:def |theorem |/--|/\*-|end |\Z))',s,re.S|re.M):
        name,b=m[1],m[2]
        if 'WeierstrassCurve' in m[0] or name in ['dualCoordinates']: continue
        b=re.sub(r':\s*ℚ','',b)
        b=re.sub(r'([A-Za-z0-9\']+) M N',lambda m:'('+str(out[m[1]])+')' if m[1] in out else m[0],b)
        try:
            out[name]=arithmetic_parse(b.replace('^','**'),{'M':M,'N':N})
        except Exception: pass
    return out

def coeff(e): return [sp.expand(e).coeff(M,4-i).coeff(N,i) for i in range(5)]
def sf(n):
    return (1 if n>0 else -1)*int(sp.prod(p for p,e in sp.factorint(abs(n)).items() if e%2))
def val(n,p):
    n=abs(n); v=0
    while n and n%p==0: v+=1; n//=p
    return v
def bit(g,i,res):
    sigma=int(res[8][i]%4==3)
    if g==-1:return sigma
    if g==2:return int(res[8][i] in [3,5])
    return (int(sp.legendre_symbol(res[g][i],g)==-1)+sigma*int(g%4==3))%2
def char(n,i,res):
    total=bit(-1,i,res) if n<0 else 0
    for p,e in sp.factorint(abs(n)).items():
        if e%2: total+=bit(int(p),i,res)
    return total%2
def mask(row):return sum(int(v)*(1<<i) for i,v in enumerate(row))

source_records=[]
cert_records=[]
inventory=[]
for rank,section,certname,oldcert,oldtex in [
    (5,'06-rank5','final155_certificate','paper/final155_certificate.json','paper/final_rank5.tex'),
    (6,'07-rank6','rank6_certificate','rank6/paper/rank6_certificate.json','rank6/paper/rank6_infinitude.tex'),
    (7,'08-rank7','rank7_certificate','rank7/paper/rank7_certificate.json','rank7/paper/rank7_infinitude.tex')]:
    p=NEW/'sections'/(section+'.tex'); s=p.read_text(); ts=tables(s)
    lp=LEAN/f'Rank{rank}.lean'; ls=lp.read_text(); ld=lean_defs(ls)
    cp=NEW/'certificates'/f'rank{rank}'/(certname+'.json'); op=OLD/oldcert
    d=json.loads(cp.read_text())
    source_records.extend([{'path':str(p),'sha256':sha(p)},{'path':str(lp),'sha256':sha(lp)},{'path':str(OLD/oldtex),'sha256':sha(OLD/oldtex)}])
    cert_records.append({'rank':rank,'updated':str(cp),'original':str(op),'updated_sha256':sha(cp),'original_sha256':sha(op),'byte_identical':cp.read_bytes()==op.read_bytes()})
    od=json.loads(op.read_text())
    ignore={'coordinate','review_status'}
    check(rank,'certificate_numerical_provenance',{k:v for k,v in d.items() if k not in ignore},{k:v for k,v in od.items() if k not in ignore},str(cp))
    cert_records[-1]['metadata_differences']=[{'key':k,'updated':d.get(k),'original':od.get(k)} for k in sorted(set(d)|set(od)) if d.get(k)!=od.get(k)]
    forms=[[x['a'],x['b']] for x in d['forms']] if rank==5 else d['forms']
    cs=d.get('cofactors',d.get('ci'))
    ft=ts[f'tab:r{rank}-'+('data' if rank==5 else 'forms')]['rows']
    if rank==5:
        got=[[numeric(ft[2][i+1]),numeric(ft[3][i+1])] for i in range(12)]; gotc=[numeric(x) for x in ft[4][1:]]
    elif rank==6:
        got=[[numeric(row[2]),numeric(row[3])] for row in ft[1:]]; gotc=[numeric(row[5]) for row in ft[1:]]
    else:
        got=[None]*12; gotc=[None]*12
        for row in ft[1:]:
            for j in [0,5]:
                i=numeric(row[j]); got[i]=[numeric(row[j+2]),numeric(row[j+3])];gotc[i]=numeric(row[j+4])
    check(rank,'linear_forms',got,forms,f'tab:r{rank}-forms/data')
    check(rank,'cofactors',gotc,cs,f'tab:r{rank}-forms/data')
    for i,(a,b) in enumerate(forms): check(rank,'Lean_linear_form',sp.expand(ld[f'L{i}']),a*M+b*N,f'Rank{rank}.L{i}')
    env={f'L{i}':a*M+b*N for i,(a,b) in enumerate(forms)}
    env.update({g:sp.prod(env[f'L{i}'] for i in range(j,j+4)) for g,j in [('F',0),('H',4),('J',8)]})
    if rank==5: env.update(D=ld['D'],D1=ld['T'],V=ld['Q'])
    if rank==6: env.update(D0=ld['d'],D1=ld['T'],D2=ld['B1'],D3=ld['B2'])
    if rank==7: env.update(D0=ld['d'],D1=ld['A1'],D2=ld['A2'],D3=ld['A3'],V1=ld['B1'],V2=ld['B2'])
    for g in ['F','H','J']:check(rank,'Lean_homogeneous_form',sp.expand(ld[g]),sp.expand(env[g]),f'Rank{rank}.{g}')
    quadratic_label='quadratics' if rank!=6 else 'D'
    qb=re.search(r'\\begin\{equation\}\\label\{r'+str(rank)+':'+quadratic_label+r'\}(.*?)\\end\{equation\}',s,re.S)[1]
    qb=re.sub(r'\\(?:begin|end)\{(?:aligned|gathered)\}','',qb).replace('&&','').replace('&=','=')
    for eq in re.split(r'\\\\|,?\s*&\s*|,\s*\\qquad',qb):
        if '=' not in eq:continue
        l,rr=eq.split('=');rr=rr.strip().rstrip(',.')
        check(rank,'quadratic_literal',sp.expand(tex(l,env)-tex(rr,env)),0,f'r{rank}:{quadratic_label}',eq)
    # Exact point coordinates from manuscript table, against the Lean definitions.
    pts=ts[f'tab:r{rank}-points']['rows'][1:]
    for k,row in enumerate(pts):
        off=0 if rank==5 else 1
        x,r=tex(row[off+1],env),tex(row[off+2],env)
        if rank==5:
            names=['P1','P2',"P'1","P'2","P'3"]; lx,ly=ld[names[k]]
        elif rank==6:
            names=['P1','P2','P3','Q1','Q2','Q3'];lx,ly=ld[names[k]+'x'],ld[names[k]+'y']
        else:
            names=['p1','p2','p3','p4','q1','q2','q3'];lx=ld[names[k]+'x'];ly=lx*ld[names[k]+'r']
        check(rank,'exact_point_abscissa',sp.expand(x-lx),0,f'tab:r{rank}-points:{names[k]}')
        check(rank,'exact_point_ordinate',sp.expand(x*r-ly),0,f'tab:r{rank}-points:{names[k]}')
    # All polynomial identities displayed in the family datum and point calculation.
    identity_labels=['identity','quartic-identities'] if rank==5 else ['FHJ','D0','identity','quartics'] if rank==6 else ['FHJ','identity','quartics']
    for lab in identity_labels:
        mm=re.search(r'\\begin\{equation\}\\label\{r'+str(rank)+':'+lab+r'\}(.*?)\\end\{equation\}',s,re.S)
        if not mm: continue
        b=mm[1]
        b=re.sub(r'\\(?:begin|end)\{aligned\}|\\(?:begin|end)\{gathered\}','',b)
        b=re.sub(r'\(\w+\)&?\\quad','',b)
        b=re.sub(r'&&\([^)]*\)','',b)
        b=b.replace(r'\qquad','')
        # FHJ broken continuation lines are merged first.
        b=re.sub(r'\\\\\s*&','',b)
        for eq in re.split(r'\\\\|,\\qquad|,\s*\\quad',b):
            eq=eq.strip().rstrip(',.')
            if not eq or '=' not in eq: continue
            eq=eq.replace('&','')
            if rank==6 and lab=='D0':
                for segment in eq.split(','):
                    if '=' in segment:
                        l,rr=segment.split('=');check(rank,'polynomial_identity',sp.expand(tex(l,env)-tex(rr,env)),0,'r6:D0')
                continue
            if eq.count('=')!=1: continue
            left,right=eq.split('=')
            check(rank,'polynomial_identity',sp.expand(tex(left,env)-tex(right,env)),0,f'r{rank}:{lab}',eq)
    # Explicit quartic coefficient tables.
    ct=ts[f'tab:r{rank}-'+('quartics' if rank<7 else 'coeff')]['rows'][1:]
    if rank==5:
        for row in ct:check(rank,'quartic_coefficient_table',[numeric(c) for c in row[1:]],coeff(tex(row[0],env)),'tab:r5-quartics:'+row[0])
    else:
        multipliers=[1764,9,441,28224,64,64] if rank==6 else [3600,16,36,1,476985600,4225,1]
        texts=['D0','3D1+65D0','D2','D0','2D1-55D0','D3'] if rank==6 else ['D0','D1','D2','D3','D0','V1','V2']
        for row,fac,poly in zip(ct,multipliers,texts):check(rank,'quartic_coefficient_table',[numeric(c) for c in row[1:]],coeff(fac*tex(poly,env)**2),f'tab:r{rank}-coeff/quartics:'+row[0])
    # CRT table and actual lattice residues; raw cofactor quotients remain signed.
    crt=ts[f'tab:r{rank}-crt']['rows']; mods=[numeric(x) for x in crt[0][1:]]
    mr=[numeric(x) for x in crt[1][1:]];nr=[numeric(x) for x in crt[2][1:]]
    lattice={'W':d['modulus'],'M0':d['M_residue'],'N0':d['N_residue']} if rank==5 else {'W':d['W'],'M0':d['M0'],'N0':d['N0']} if rank==6 else d['lattice']
    lattice={k:int(v) for k,v in lattice.items()}
    check(rank,'CRT_modulus',int(sp.prod(mods)),lattice['W'],f'tab:r{rank}-crt')
    for q,m,n in zip(mods,mr,nr):check(rank,'CRT_residues',[lattice['M0']%q,lattice['N0']%q],[m%q,n%q],f'tab:r{rank}-crt:{q}')
    for k,v in lattice.items():check(rank,'lattice_literal_present',bool(re.search(r'\b'+str(v)+r'\b',s)),True,f'chapter rank {rank}: {k}')
    raw=[(a*lattice['M0']+b*lattice['N0']) for a,b in forms]
    for i,n in enumerate(raw):check(rank,'cofactor_integrality',n%cs[i],0,f'Rank{rank}:L{i}/c{i}')
    ps=[n//c for n,c in zip(raw,cs)]
    rt=ts[f'tab:r{rank}-'+('residues' if rank<7 else 'res')]['rows'][1:]
    res={}
    if rank==6:
        for qi,q in enumerate([8,3,5,7,11,17,23]):res[q]=[numeric(row[3+qi]) for row in rt]
        for i,row in enumerate(rt):check(rank,'signed_anchor_values',[numeric(row[1]),numeric(row[2])],[forms[i][0]*19+forms[i][1]*11,(forms[i][0]*19+forms[i][1]*11)//cs[i]],f'tab:r6-residues:{i}')
    else:
        for row in rt:
            q=int(re.findall(r'\d+',row[0])[-1]);res[q]=[numeric(x) for x in row[1:]]
    for q,vals in res.items():check(rank,'prime_residue_table',vals,[p%q for p in ps],f'tab:r{rank}-residues:{q}')
    # Constant Legendre characters, with reciprocity correction from the fixed prime residue.
    chars=ts[f'tab:r{rank}-'+('const-char' if rank==5 else 'chars' if rank==6 else 'lambda')]['rows'][1:]
    for row in chars:
        g=int(re.findall(r'-?\d+',row[0])[-1]);check(rank,'constant_character_table',[numeric(c) for c in row[1:]],[bit(g,i,res) for i in range(12)],f'tab:r{rank}-characters:{g}')
    # Cross symbols recomputed independently using the same literal reciprocity formula.
    cross=ts[f'tab:r{rank}-'+('cross' if rank<7 else 'gamma')]['rows'][1:]
    gamma=[[None]*12 for _ in range(12)]
    for i in range(12):
        for j in range(12):
            if i==j:continue
            if i==0:gamma[i][j]=char(forms[j][1]*cs[j],0,res)
            elif j==0:gamma[i][j]=(char(forms[i][1]*cs[i],0,res)+bit(-1,0,res)*bit(-1,i,res))%2
            elif not (4<=i<=7 and 4<=j<=7 or 8<=i<=11 and 8<=j<=11):
                if i<j:
                    K=cs[0]*cs[j]*forms[i][1]*(forms[j][0]*forms[i][1]-forms[i][0]*forms[j][1])
                    gamma[i][j]=(char(K,i,res)+gamma[i][0])%2
                else:gamma[i][j]=(gamma[j][i]+bit(-1,i,res)*bit(-1,j,res))%2
    for i,row in enumerate(cross):
        for j,c in enumerate(row[1:]):
            if c in ['0','1']:check(rank,'cross_character_table',numeric(c),gamma[i][j],f'tab:r{rank}-gamma:{i},{j}')
    # The literal matrix tables and both eta variants agree with checked owner code.
    mattext=(LEAN/'MatrixCertificates.lean').read_text().split('namespace Rank'+str(rank)+'\n')[1].split('\nend Rank')[0]
    for key,lab in [('E0','ME'),('Ep0','MEp')]:
        rows=ts[f'tab:r{rank}-{lab}']['rows'][1:]
        codes=[mask([numeric(c) for c in row[2:]]) for row in rows]
        check(rank,'matrix_literal',codes,d['matrices'][key],f'tab:r{rank}-{lab}')
        for variant in [key,key.replace('0','1')]:
            mm=re.search(r'^def '+variant+r' : List ℕ := \[([^]]*)\]',mattext,re.M)
            check(rank,'Lean_matrix_literal',[int(x) for x in mm[1].split(',')],d['matrices'][variant],f'MatrixCertificates.Rank{rank}.{variant}')
    for key,name in [('E','Egenerators'),('Ep','Epgenerators')]:
        mm=re.search(r'^def '+name+r' : List ℕ := \[([^]]*)\]',mattext,re.M)
        check(rank,'Lean_kernel_generators',[int(x) for x in mm[1].split(',')],d.get('known_vectors',d.get('known_codes'))[key],f'MatrixCertificates.Rank{rank}.{name}')
    if rank==7:
        vr=ts['tab:r7-vectors']['rows']
        vals=[mask([numeric(c) for c in row[1:]]) for row in vr if row[0].startswith(r'\delta')]
        check(rank,'manuscript_kernel_generators',vals,d['known_codes']['E']+d['known_codes']['Ep'],'tab:r7-vectors')
    # The class codes themselves follow from the actual displayed abscissas,
    # including the torsion coefficients, after L_i = c_i p_i.
    pp=sp.symbols('p0:12');penv={f'L{i}':cs[i]*pp[i] for i in range(12)}
    penv.update({g:sp.prod(penv[f'L{i}'] for i in range(j,j+4)) for g,j in [('F',0),('H',4),('J',8)]})
    B={5:2700,6:784,7:33124}[rank];C={5:57600,6:1764,7:9}[rank]
    consts=[-1,2,3,5] if rank==5 else [-1,2,3,7] if rank==6 else [-1,2,3,7,13]
    ecnt=2 if rank==5 else 3 if rank==6 else 4
    xexpr=[tex(row[(1 if rank==5 else 2)],penv) for row in pts]
    allx=[-B*penv['F']*penv['H']]+xexpr[:ecnt]+[C*penv['F']*penv['J']]+xexpr[ecnt:]
    allcodes=[]
    for q,e in enumerate(allx):
        base=list(range(8)) if q<=ecnt else [0,1,2,3,8,9,10,11]
        fac=sp.Poly(e,*pp).terms();assert len(fac)==1
        powers,z=fac[0];z=sp.Rational(z);fz=sf(int(z.p*z.q))
        cc=[int(fz<0)]+[int(sp.factorint(abs(fz)).get(c,0)%2) for c in consts[1:]]
        cc += [powers[i]%2 for i in base]
        allcodes.append(mask(cc))
    expectedcodes=d.get('known_vectors',d.get('known_codes'))
    check(rank,'actual_point_squareclass_codes',allcodes,expectedcodes['E']+expectedcodes['Ep'],f'tab:r{rank}-classes')
    # Signed determinant factorization tables are independently recomputed.
    if rank in [5,7]:
        for row in ts[f'tab:r{rank}-det']['rows'][1:]:
            for j in [0,2,4]:
                i,k=map(int,re.findall(r'\d+',row[j]));dv=forms[i][0]*forms[k][1]-forms[k][0]*forms[i][1]
                check(rank,'determinant_table',numeric(row[j+1]),dv,f'tab:r{rank}-det:{i},{k}')
    if 'determinant_factorizations' in d:
        for dd in d['determinant_factorizations']:
            i,j=dd['i'],dd['j'];check(rank,'determinant_certificate',dd['value'],forms[i][0]*forms[j][1]-forms[j][0]*forms[i][1],f'certificate determinant:{i},{j}')
    # All squarefree reciprocity operands in the detailed tables.
    if rank in [5,6]:
        width=3 if rank==5 else 6
        for row in ts[f'tab:r{rank}-K']['rows'][1:]:
            for off in range(0,len(row),width):
                if not row[off]:continue
                i,j=map(int,re.findall(r'\d+',row[off]));dv=forms[j][0]*forms[i][1]-forms[i][0]*forms[j][1];f=cs[j]*forms[i][1];K=cs[0]*f*dv
                if rank==5:
                    check(rank,'reciprocity_squarefree_operand',numeric(row[off+1]),sf(K),f'tab:r5-K:{i},{j}')
                    check(rank,'reciprocity_operand_character',numeric(row[off+2]),char(K,i,res),f'tab:r5-K:{i},{j}')
                else:
                    actual=[numeric(x) for x in row[off+1:off+6]]
                    check(rank,'reciprocity_operand_row',actual,[dv,f,sf(K),char(K,i,res),gamma[i][j]],f'tab:r6-K:{i},{j}')
    if rank==6:
        for row in ts['tab:r6-pivot']['rows'][1:]:
            i=numeric(row[0]);bc=forms[i][1]*cs[i]
            check(rank,'pivot_operand_row',[numeric(x) for x in row[1:]], [bc,bc,sf(bc),char(bc,0,res),bit(-1,i,res),gamma[i][0]],f'tab:r6-pivot:{i}')
    if rank==7:
        rec=ts['tab:r7-recip']['rows']
        check(rank,'pivot_squarefree_operands',[numeric(x) for x in rec[1][1:]],[sf(forms[i][1]*cs[i]) for i in range(1,12)],'tab:r7-recip:sj')
        check(rank,'pivot_squarefree_characters',[numeric(x) for x in rec[2][1:]],[char(forms[i][1]*cs[i],0,res) for i in range(1,12)],'tab:r7-recip:lambda0')
        for row in rec[4:7]+rec[8:12]:
            i=int(re.findall(r'\d+',row[0])[-1]);start=2 if i<=3 else 8
            for j,c in enumerate(row[1:],start):
                if not c:continue
                K=cs[0]*cs[j]*forms[i][1]*(forms[j][0]*forms[i][1]-forms[i][0]*forms[j][1])
                check(rank,'reciprocity_squarefree_operand',numeric(c),sf(K),f'tab:r7-recip:{i},{j}')
        for row in ts['tab:r7-anchor']['rows'][1:]:
            i=numeric(row[0]);z=forms[i][0]*18+forms[i][1]*11
            check(rank,'signed_anchor_row',[numeric(c) for c in row[1:]],[z,val(z,2),val(z,3),cs[i],z//cs[i],(z//cs[i])%8,(z//cs[i])%3],f'tab:r7-anchor:{i}')
        for row in ts['tab:r7-raw']['rows'][1:]:
            q=numeric(row[0]);m,n=map(int,re.findall(r'\d+',row[1]));check(rank,'raw_CRT_form_values',[numeric(c) for c in row[2:]],[(a*m+b*n)%q for a,b in forms],f'tab:r7-raw:{q}')
    if rank==6:
        zs=[70*sp.prod(raw[:4]),-784*sp.prod(raw[:4])*sp.prod(raw[4:8]),-140*sp.prod(raw[:4]),1764*sp.prod(raw[:4])*sp.prod(raw[8:])]
        for row,z in zip(ts['tab:r6-coeffs']['rows'][1:],zs):
            z=int(z);vv=[]
            for p,q in [(2,8),(3,3),(7,7)]:v=val(z,p);vv.extend([v,(z//p**v)%q])
            check(rank,'fixed_coefficient_valuation_units',[numeric(c) for c in row[1:]],vv,'tab:r6-coeffs:'+row[0])
    if rank in [5,7]:
        diag=ts[f'tab:r{rank}-'+('diagonal' if rank==5 else 'diag')]['rows'][2:]
        for row in diag:
            i=numeric(row[0]);ke=char(-1 if rank==5 else -2,i,res);kep=char(2 if rank==5 else 3,i,res)
            se=sum(gamma[i][j] for j in range(8) if j!=i);sep=sum(gamma[i][j] for j in [0,1,2,3,8,9,10,11] if j!=i)
            check(rank,'diagonal_operand_row',[numeric(c) for c in row[1:]],[ke,se if rank==5 else se%2,(ke+se)%2,kep,sep if rank==5 else sep%2,(kep+sep)%2],f'tab:r{rank}-diagonal:{i}')
    if rank==5:
        vv=re.search(r'\\label\{r5:class-vectors\}(.*?)\\end\{equation\}',s,re.S)[1]
        # TeX alignment uses &=&, so take the final parenthesis of each displayed line.
        codes=[mask(map(int,re.findall(r'\b[01]\b',line[line.rfind('('):]))) for line in vv.splitlines() if '\\mathbf ' in line]
        check(rank,'manuscript_kernel_generators',codes,expectedcodes['E']+expectedcodes['Ep'],'r5:class-vectors')
        fr=ts['tab:r5-fixed-rows']['rows'][1:]
        for row,expected in zip(fr,[[1,0,1,0],[0,0,1,1],[1,1,0,1],[0,0,1,0],[0,1,1,0],[0,0,1,1],[0,1,1,0],[1,0,0,0]]):
            check(rank,'fixed_row_constant_coordinates',[numeric(c) for c in row[3:7]],expected,'tab:r5-fixed-rows:'+row[0])
        mr=ts['tab:r5-minors']['rows'];blocks=[(mr[1:10],'E0',[3,0,6,4,12,2,5,8,7],[2,0,1,11,3,8,4,5,6]),(mr[11:19],'Ep0',[2,3,4,5,7,9,6,10],[0,4,1,6,2,3,5,11])]
        for rows,key,ri,ci in blocks:
            for row,i in zip(rows,ri):check(rank,'triangular_minor_literal',[numeric(c) for c in row[1:]],[(d['matrices'][key][i]>>j)&1 for j in ci],'tab:r5-minors:'+row[0])
        fp=re.search(r'\\label\{r5:five-points\}(.*?)\\end\{equation\}',s,re.S)[1]
        lines=[line for line in fp.splitlines() if '&=' in line]
        for line,name in zip(lines,['P1','P2','P3','P4','P5']):
            coords=line.split('&=')[1]
            coords=re.sub(r'\\(?:Big|big|left|right)','',coords).strip().rstrip('\\').strip().rstrip(',')
            assert coords[0]=='(' and coords[-1]==')'
            x,y=coords[1:-1].split(',',1)
            check(rank,'five_displayed_points_literal',tuple(map(sp.expand,(tex(x,env),tex(y,env)))),tuple(map(sp.expand,ld[name])),'r5:five-points:'+name)
    if rank==6:
        cb=ts['tab:r6-coords']['rows'][2:]
        for row,z in zip(cb,[-1,2,3,7]):
            u2=z//2**val(z,2);u3=z//3**val(z,3);u7=z//7**val(z,7)
            exp=[int(u2%8 in [3,7]),val(z,2)%2,int(u2%8 in [3,5]),val(z,3)%2,int(sp.legendre_symbol(u3,3)==-1),val(z,7)%2,int(sp.legendre_symbol(u7,7)==-1),int(z<0)]
            check(rank,'fixed_local_constant_coordinates',[numeric(c) for c in row[1:]],exp,'tab:r6-coords:'+row[0])
        sb=re.search(r'\\label\{r6:samegroup\}(.*?)\\end\{equation\}',s,re.S)[1]
        for segment in re.split(r'\\quad|\\\\',sb):
            pairs=re.findall(r'\\Delta_\{(\d+),(\d+)\}',segment)
            if not pairs:continue
            rhs=segment.split('=')[-1].strip().rstrip(',.')
            if '\\end' in rhs:rhs=rhs.split('\\end')[0].strip().rstrip(',.')
            v=numeric(rhs)
            for i,j in pairs:
                i,j=int(i),int(j);check(rank,'same_group_determinant_literal',v,forms[i][0]*forms[j][1]-forms[j][0]*forms[i][1],f'r6:samegroup:{i},{j}')
    if rank==7:
        coords=ts['tab:r7-coords']['rows'][1:]
        zs=[-1,2,3,7,13]
        expected=[]
        expected.append([(int((z//2**val(z,2))%8 in [3,7]),val(z,2)%2,int((z//2**val(z,2))%8 in [3,5])) for z in zs])
        for p in [3,7,13]:expected.append([(int(sp.legendre_symbol(z//p**val(z,p),p)==-1),val(z,p)%2) for z in zs])
        expected.append([int(z<0) for z in zs])
        for row,exp in zip(coords,expected):
            actual=[tuple(map(int,re.findall(r'\d+',c))) if '(' in c else numeric(c) for c in row[1:]]
            check(rank,'fixed_local_constant_coordinates',actual,exp,'tab:r7-coords:'+row[0])
        zf,zh,zj=[int(sp.prod(raw[j:j+4])) for j in [0,4,8]]
        aa=91205*zf;bb=-33124*zf*zh;bc=9*zf*zj
        actual=[[val(aa,2),(aa//2**val(aa,2))%8,val(bb,2),(bb//2**val(bb,2))%8,val(bc,2),(bc//2**val(bc,2))%8],
                [val(aa,3),(aa//3**val(aa,3))%3,val(bb,3),(bb//3**val(bb,3))%3,val(bc,3)],
                [aa%7,val(bb,7),(bb//7**val(bb,7))%7,bc%7],
                [aa%13,val(bb,13),(bb//13**val(bb,13))%13,bc%13]]
        for p,got,exp in zip([2,3,7,13],actual,[[7,5,13,7,14,3],[4,1,8,1,13],[1,2,1,1],[12,2,7,1]]):check(rank,'fixed_coefficient_valuation_units',got,exp,'tab:r7-coef-local:'+str(p))
    for lab,t in ts.items():inventory.append({'rank':rank,'label':lab,'line':t['line'],'data_rows':len(t['rows'])-1})

coverage=[
 {'statement':'thm:r5, thm:r6, thm:r7: exact Mordell-Weil rank at each prime specialization',
  'status':'covered for the same literal CRT lattice and positive distinct prime outputs',
  'Lean':['RankCertificates.Rank5ExactRank.hasExactRank','RankCertificates.Rank6ExactRank.hasExactRank','RankCertificates.Rank7ExactRank.hasExactRank'],
  'qualification':'These endpoints have no cone premise. The manuscript prime-specialization condition avoids the full intrinsic set S; the core hypothesis only needs the smaller fixed column primes and explicit distinctness. Rewriting (M,N) as the literal CRT lattice is necessary to apply the endpoints.'},
 {'statement':'thm:r5, thm:r6, thm:r7: unconditional infinitude in the stated progression and cone',
  'status':'not supplied by the existing unconditional core',
  'qualification':'Existing extraction endpoints still take actual Mangoldt/cyclic prime mass hypotheses. Neither arithmetic data equivalence nor an inverse-Gowers theorem supplies that prime-pattern analytic input.'},
 {'statement':'prop:r5-five-points: the exact five displayed points are Z-linearly independent',
  'status':'coordinate identities and nonsingular memberships covered; actual point independence not yet an existing Lean endpoint',
  'Lean':['Rank5.P1_onCurve','Rank5.P2_onCurve','Rank5.P3_onCurve','Rank5.P4_onCurve','Rank5.P5_onCurve','Rank5.P3_dualCoordinates','Rank5.P4_dualCoordinates','Rank5.P5_dualCoordinates','RankCertificates.RankLowerBounds.rank_lowerBound_of_twoIsogeny_images'],
  'required_new_proof':'An actual group-theoretic adapter must show these five points generate a subgroup of full rank (using the two quotient image bases, dual-isogeny composition, and finite generation), then conclude LinearIndependent over Z. Existing LinearIndependent declarations concern ZMod 2 squareclasses or binary vectors; a cardinality rank bound alone is not this claim.'},
 {'statement':'lem:r5-fixed, lem:r6-fixed, lem:r7-fixed: full local images on E(Q_p), E\u2032(Q_p), and E\u2032(R)',
  'status':'necessary restrictions on actual rational-point images covered; standalone full-local-field assertions not covered',
  'Lean':['Rank5OddRows.three_actualImage','Rank5OddRows.five_E_actualImage','Rank5OddRows.five_Ep_actualImage','Rank5ExactRank.fixedFunctionalE_zero','Rank5ExactRank.fixedFunctionalEp_zero','Rank6ExactRank.characterFamilyE_zero','Rank6ExactRank.characterFamilyEp_zero','Rank7ExactRank.E_fixed_rows','Rank7ExactRank.Ep_fixed_rows'],
  'required_new_proof':'Generalize the valuation/descent maps and images to all local-field points and instantiate the stated inclusions/equalities. In particular rank6 E(Q_3)={1}, rank7 E(Q_3)={1}, rank7 E\u2032(Q_7)=E\u2032(Q_13)={1}, and the full real-image equalities are stronger standalone statements than rational-image character vanishing. The latter are sufficient for the already checked rational exact-rank theorem.'}
]
cones=[
 {'rank':5,'original_and_updated':'M>0 and 19M/20<N<11M/10','changed':False,
  'additional_updated_observation':'All twelve forms are positive exactly for M>0 and 55M/62<N<3M; this does not redefine the chosen cone.',
  'core_sector':'x,y in [20T,21T]','scope':'Its translated lattice lies in the chosen cone for all sufficiently large T. The existing core does not state this exact cone-membership wrapper.'},
 {'rank':6,'original_and_updated':'N>0 and 29N<M<31N','changed':False,
  'core_sector':'x in [60T,61T], y in [T,2T]',
  'scope':'This sector contains points with M/N near 60 and fails the upper bound M<31N. It meets the paper cone but no existing extraction theorem restricts the mass to that intersection. The core exact-rank statement needs only positive outputs, so its arithmetic conclusion is not affected.'},
 {'rank':7,'original_and_updated':'N>0 and 2999N<M<3001N','changed':False,
  'core_sector':'x in [8000T,8001T], y in [T,2T]',
  'scope':'For every T>=1 the whole translated sector has M>3001N, outside the paper cone. At the minimum x=8000T,y=2T, M-3001N=1998WT+M0-3001N0>0 already at T=1. The existing sector infinitude statement therefore cannot establish infinitude inside the paper cone.'}
]
extra_sources=['MatrixCertificates.lean','RankLowerBounds.lean','Rank5ExactRank.lean','Rank6ExactRank.lean','Rank7ExactRank.lean','Rank5OddRows.lean','LiteralAffineSystems.lean','LiteralCyclicBridge.lean','PrimeSpecializations.lean','DescentWitnesses.lean']
source_records.extend({'path':str(LEAN/x),'sha256':sha(LEAN/x)} for x in extra_sources)
result={'scope':'Independent read-only literal comparison of updated family chapters with original archive certificates and existing checked Lean owners. This is a transcription audit, not a new kernel proof or a proof of prime-pattern infinitude.',
        'archive_scripts_executed':False,'core_files_modified':False,
        'audit_script':{'path':str(Path(__file__)),'sha256':sha(Path(__file__))},
        'sources':source_records,'certificates':cert_records,'table_inventory':inventory,'checks':checks,'check_count':len(checks),'failed_checks':[c for c in checks if not c['match']],
        'literal_conclusion':('All 1176 checked arithmetic/transcription comparisons match. No numerical datum change requires a new Lean proof. Certificate rank5 metadata was edited; rank6 and rank7 certificates are byte-identical to the originals.' if len(checks) == EXPECTED_CHECK_COUNT and not any(not c['match'] for c in checks) else 'The reproduction did not pass all expected comparisons; inspect failed_checks and check_count.'),
        'expected_check_count':EXPECTED_CHECK_COUNT,'check_count_matches_expected':len(checks)==EXPECTED_CHECK_COUNT,
        'dependencies':{'python':platform.python_version(),'sympy':sp.__version__},
        'input_roots':{'updated':str(NEW),'original':str(OLD),'lean_modules':str(LEAN)},
        'statement_coverage':coverage,'cone_and_progression_comparison':cones,
        'additional_standalone_proof_obligations':['Actual Z-linear independence of the exact five displayed rank5 points','Full Qp and R local-image assertions, if those standalone lemmas are included in the formalization target','An infinitude adapter for the manuscript-specific narrow rank6 and rank7 cones','The actual unconditional prime-pattern analytic supplier already identified by the parent audit']}
OUTPUT.parent.mkdir(parents=True, exist_ok=True)
OUTPUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'failures':[{k:v for k,v in c.items() if k not in ['actual','expected']} for c in result['failed_checks']]},indent=2))

if len(checks) != EXPECTED_CHECK_COUNT or result['failed_checks']:
    sys.exit(1)
