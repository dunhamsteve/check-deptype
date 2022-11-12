-- module Tartlet

import Data.List
import Data.String.Parser
import System.REPL

%hide Nat

Name = String
Message = String

M a = Either Message a

failure : String -> M a
failure = Left

data Expr
    = Var Name             -- x
    | Pi Name Expr Expr    -- (Π ((X A)) B)
    | Lambda Name Expr     -- (λ (x) b)
    | App Expr Expr        -- (rator rand)
    | Sigma Name Expr Expr -- Σ ((x A) D)
    | Cons Expr Expr       -- (cons a d)
    | Car Expr             -- (car e)
    | Cdr Expr             -- (cdr d)
    | Nat
    | Zero
    | Add1 Expr            -- (add1 e)
    | IndNat Expr Expr Expr Expr -- (ind-Nat tgt mot base step)
    | Equal Expr Expr Expr -- (= A from to)
    | Same
    | Replace Expr Expr Expr
    | Trivial
    | Sole
    | Absurd
    | IndAbsurd Expr Expr
    | Atom
    | Tick String
    | U
    | The Expr Expr

-- we need eq show..


freshen : List Name -> Name -> Name
freshen used x = if elem x used then freshen used $ x ++ "'" else x

aEquivHelper : Integer -> 
               List (Name,Integer) -> Expr ->
               List (Name,Integer) -> Expr ->
               Bool

aEquivHelper i xs (Var x) ys (Var y) =
    case (lookup x xs, lookup y ys) of
        (Nothing,Nothing) => x == y
        (Just i, Just j) => i == j
        _ => False

aEquivHelper i xs (Pi x a1 r1) ys (Pi y a2 r2) =
    aEquivHelper i xs a1 ys a2 && aEquivHelper (i+1) ((x,i)::xs) r1 ((y,i)::ys) r2

aEquivHelper i xs (Lambda x body1) ys (Lambda y body2) =
    aEquivHelper (i+1) ((x,i)::xs) body1 ((y,i)::ys) body2

aEquivHelper i xs (App rator1 rand1) ys (App rator2 rand2) =
    aEquivHelper i xs rator1 ys rator2 && aEquivHelper i xs rand1 ys rand2

aEquivHelper i xs (Sigma x a1 r1) ys (Sigma y a2 r2) =
    aEquivHelper i xs a1 ys a2 && aEquivHelper (i+1) ((x,i)::xs) r1 ((y,i)::ys) r2

aEquivHelper _ _ (Tick a1) _ (Tick a2) = a1 == a2
aEquivHelper _ _ (The Absurd _) _ (The Absurd _) = True

aEquivHelper i xs (The t1 x) ys (The t2 y) =
    aEquivHelper i xs t1 ys t2 && aEquivHelper i xs x ys y



--     -- ... lots of just follow args...
aEquivHelper i xs (Cons x1 x2) ys  (Cons y1 y2) =
    aEquivHelper i xs x1 ys y1 && 
    aEquivHelper i xs x2 ys y2
aEquivHelper i xs (Car x) ys (Car y) = aEquivHelper i xs x ys y
aEquivHelper i xs (Cdr x) ys (Cdr y) = aEquivHelper i xs x ys y
aEquivHelper i xs Nat ys Nat = True
aEquivHelper i xs Zero ys Zero = True
aEquivHelper i xs (Add1 x) ys (Add1 y) = aEquivHelper i xs x ys y
aEquivHelper i xs (IndNat x1 x2 x3 x4) ys (IndNat y1 y2 y3 y4) =
    aEquivHelper i xs x1 ys y1 && 
    aEquivHelper i xs x2 ys y2 && 
    aEquivHelper i xs x3 ys y3 && 
    aEquivHelper i xs x4 ys y4
aEquivHelper i xs (Equal x1 x2 x3) ys (Equal y1 y2 y3) =
    aEquivHelper i xs x1 ys y1 && 
    aEquivHelper i xs x2 ys y2 && 
    aEquivHelper i xs x3 ys y3
aEquivHelper i xs Same ys Same = True
aEquivHelper i xs (Replace x1 x2 x3) ys (Replace y1 y2 y3) =
    aEquivHelper i xs x1 ys y1 && 
    aEquivHelper i xs x2 ys y2 && 
    aEquivHelper i xs x3 ys y3
aEquivHelper i xs Trivial ys Trivial = True
aEquivHelper i xs Sole ys Sole = True
aEquivHelper i xs Absurd ys Absurd = True
aEquivHelper i xs (IndAbsurd x1 x2) ys (IndAbsurd y1 y2) =
    aEquivHelper i xs x1 ys y1 && 
    aEquivHelper i xs x2 ys y2
aEquivHelper i xs Atom ys Atom = True
aEquivHelper i xs U ys U = True
aEquivHelper _ _ _ _ _ = False
               
aEquiv : Expr -> Expr -> Bool
aEquiv e1 e2 = aEquivHelper 0 [] e1 [] e2

mutual
    Ty = Value
    
    data Value
        = VPi Ty Closure
        | VLambda Closure
        | VSigma Ty Closure
        | VPair Value Value
        | VNat
        | VZero
        | VAdd1 Value
        | VEq Ty Value Value
        | VSame
        | VTrivial
        | VSole
        | VAbsurd
        | VAtom
        | VTick String
        | VU
        | VNeutral Ty Neutral
    
    record Closure where
        constructor MkCl
        env : Env
        name : Name
        body : Expr
    
    data Env = ENV (List (Name,Value))

    extendEnv : Env -> Name -> Value -> Env
    extendEnv (ENV env) x v = ENV $ (x,v) :: env

    evalVar : Env -> Name -> M Value
    evalVar (ENV []) x = failure "Missing value for \{show x}"
    evalVar (ENV ((y,v)::env)) x = if y == x
        then pure v
        else evalVar (ENV env) x
    

    data Neutral
        = NVar Name
        | NApp Neutral Normal
        | NCar Neutral
        | NCdr Neutral
        | NIndNat Neutral Normal Normal Normal
        | NReplace Neutral Normal Normal
        | NIndAbsurd Neutral Normal
    
    data Normal = MkNorm Ty Value

data CtxEntry = Def Ty Value | IsA Ty

data Ctx = CX (List (Name,CtxEntry))

initCtx : Ctx
initCtx = CX []

ctxNames : Ctx -> List Name
ctxNames (CX ctx) = map fst ctx

extendCtx : Ctx -> Name -> Ty -> Ctx
extendCtx (CX ctx) x t = CX ((x, IsA t)::ctx)

define : Ctx -> Name -> Ty -> Value -> Ctx
define (CX ctx) x t v = CX ((x, Def t v)::ctx)

lookupType : Ctx -> Name -> M Ty
lookupType (CX []) x = failure "Unbound variable \{show x}"
lookupType (CX ((y,e)::ctx)) x = 
    if x == y
    then case e of
        Def t _ => pure t
        IsA t   => pure t
    else lookupType (CX ctx) x

mkEnv : Ctx -> Env
mkEnv (CX []) = ENV []
mkEnv (CX ((x,e)::ctx)) =
    let ENV env = mkEnv (CX ctx)
        v = case e of
            Def _ v => v
            IsA t => VNeutral t (NVar x)
    in ENV ((x,v)::env)

mutual
    eval : Env -> Expr -> M Value
    eval env (Var x) = evalVar env x
    eval env (Pi x dom ran) = pure $ VPi !(eval env dom) (MkCl env x ran)
    eval env (Lambda x body) = pure $ VLambda (MkCl env x body)
    eval env (App rator rand) = doApply !(eval env rator) !(eval env rand)
    eval env (Sigma x carTy cdrTy) = pure $ VSigma !(eval env carTy) (MkCl env x cdrTy)
    eval env (Cons a d) = pure $ VPair !(eval env a) !(eval env d)
    eval env (Car e) = doCar !(eval env e)
    eval env (Cdr e) = doCdr !(eval env e)
    eval env Nat = pure VNat
    eval env Zero = pure VZero
    eval env (Add1 e) = pure $ VAdd1 !(eval env e)
    eval env (IndNat tgt mot base step) = doIndNat !(eval env tgt) !(eval env mot) !(eval env base) !(eval env step)
    eval env (Equal ty from to) = pure $ VEq !(eval env ty) !(eval env from) !(eval env to)
    eval env Same = pure VSame
    eval env (Replace tgt mot base) = doReplace !(eval env tgt) !(eval env mot) !(eval env base)
    eval env Trivial = pure VTrivial
    eval env Sole = pure VSole
    eval env Absurd = pure VAbsurd
    eval env (IndAbsurd tgt mot) = doIndAbsurd !(eval env tgt) !(eval env mot)
    eval env Atom = pure VAtom
    eval env (Tick x) = pure (VTick x)
    eval env U = pure VU
    eval env (The ty e) = eval env e

    evalClosure : Closure -> Value -> M Value
    evalClosure (MkCl env x e) v = eval (extendEnv env x v) e

    doCar : Value -> M Value
    doCar (VPair a d) = pure a
    doCar (VNeutral (VSigma aT dT) neu) = pure $ VNeutral aT (NCar neu)
    doCar v = failure "doCar called on bad value" -- no show yet

    doCdr : Value -> M Value
    doCdr (VPair a d) = pure d
    doCdr v@(VNeutral (VSigma aT dT) neu) =
        pure $ VNeutral !(evalClosure dT !(doCar v)) (NCdr neu)
    doCdr v = failure "doCdr called on bad value"

    doApply : Value -> Value -> M Value
    doApply (VLambda closure) arg = evalClosure closure arg
    doApply (VNeutral (VPi dom ran) neu) arg =
        pure $ VNeutral !(evalClosure ran arg) (NApp neu (MkNorm dom arg))
    doApply v arg = failure "doApply called on bad value"

    doIndAbsurd : Value -> Value -> M Value
    doIndAbsurd (VNeutral VAbsurd neu) mot =
        pure $ VNeutral mot (NIndAbsurd neu (MkNorm VU mot))
    doIndAbsurd _ _ = failure "doIndAbsurd called with bad value"

    doReplace : Value -> Value -> Value -> M Value
    doReplace VSame mot base = pure base
    doReplace (VNeutral (VEq ty from to) neu) mot base =
        let motT = VPi ty (MkCl (ENV []) "x" U)
            baseT = doApply mot from
        in pure $ VNeutral !(doApply mot to)
                        (NReplace neu (MkNorm motT mot) (MkNorm !baseT base))
    doReplace _ _ _ = failure "bad args doReplace"

    indNatStepType : Value -> M Value
    indNatStepType mot =
        eval (ENV [("mot", mot)])
            (Pi "n-1" Nat
                (Pi "almost" (App (Var "mot") (Var "n-1"))
                (App (Var "mot") (Add1 (Var "n-1")))))

    doIndNat : Value -> Value -> Value -> Value -> M Value
    doIndNat VZero mot base step = pure base
    doIndNat (VAdd1 v) mot base step =
        doApply !(doApply step v) !(doIndNat v mot base step)
    doIndNat tgt@(VNeutral VNat neu) mot base step =
        pure $ VNeutral !(doApply mot tgt)
            (NIndNat neu
                (MkNorm (VPi VNat (MkCl (ENV []) "k" U)) mot)
                (MkNorm !(doApply mot VZero) base)
                (MkNorm !(indNatStepType mot) step))
    doIndNat _ _ _ _ = failure "Bad args doIndNat"




readBackNeutral : {auto ctx: Ctx} -> Neutral -> M Expr

-- REVIEW - is there a cata here?
readBackTyped : Ctx -> Ty -> Value -> M Expr
readBackTyped ctx VNat VZero = pure Zero
readBackTyped ctx VNat (VAdd1 v) = pure $ Add1 !(readBackTyped ctx VNat v)
readBackTyped ctx (VPi dom ran) fun =
    let x = freshen (ctxNames ctx) ran.name
        xVal = VNeutral dom (NVar x)
    in pure $ Lambda x
        !(readBackTyped
            (extendCtx ctx x dom)
            !(evalClosure ran xVal)
            !(doApply fun xVal))

-- mixing do with ! because I don't have good names for the intermediates
readBackTyped ctx (VSigma aT dT) pair = do
    carVal <- doCar pair
    cdrVal <- doCdr pair    
    pure $ Cons !(readBackTyped ctx aT carVal) !(readBackTyped ctx !(evalClosure dT carVal) cdrVal)

readBackTyped ctx VTrivial _ = pure Sole
readBackTyped ctx VAbsurd (VNeutral VAbsurd neu) =
    pure $ The Absurd !(readBackNeutral neu)
readBackTyped ctx (VEq _ _ _) VSame = pure Same
readBackTyped ctx VAtom (VTick x) = pure $ Tick x
readBackTyped ctx VU VNat = pure Nat
readBackTyped ctx VU VAtom = pure Atom
readBackTyped ctx VU VTrivial = pure Trivial
readBackTyped ctx VU VAbsurd = pure Absurd
readBackTyped ctx VU (VEq t from to) =
    pure $ Equal !(readBackTyped ctx VU t)
                 !(readBackTyped ctx t from)
                 !(readBackTyped ctx t to)
readBackTyped ctx VU (VSigma aT dT) =
    let x = freshen (ctxNames ctx) dT.name
        a = readBackTyped ctx VU aT
        d = readBackTyped (extendCtx ctx x aT)
            VU
            !(evalClosure dT (VNeutral aT (NVar x)))
     in pure $ Sigma x !a !d
readBackTyped ctx VU (VPi aT bT) = do
    let x = freshen (ctxNames ctx) bT.name
    a <- readBackTyped ctx VU aT
    bT' <- (evalClosure bT (VNeutral aT (NVar x)))
    b <- readBackTyped (extendCtx ctx x aT) VU bT'
    pure $ Pi x a b
readBackTyped ctx VU VU = pure U
readBackTyped ctx t (VNeutral t' neu) = readBackNeutral neu
readBackTyped _ otherT otherE = failure $ "bad args readBackTyped"

readBackNormal : {auto ctx : Ctx} -> Normal -> M Expr
readBackNormal (MkNorm t v) = readBackTyped ctx t v

readBackNeutral (NVar x) = pure $ Var x
-- there could almost be a readBack typeclass ...
-- and we could probably implicit in the ctx to be more idrisy.
readBackNeutral (NApp neu arg) = [| App (readBackNeutral neu) (readBackNormal arg) |]
readBackNeutral (NCar neu) = [| Car (readBackNeutral neu) |] 
readBackNeutral (NCdr neu) = [| Cdr (readBackNeutral neu) |] 
readBackNeutral (NIndNat neu mot base step) = 
    [| IndNat (readBackNeutral neu)
              (readBackNormal mot)
              (readBackNormal base)
              (readBackNormal step) |]
readBackNeutral (NReplace neu mot base) =
    [| Replace (readBackNeutral neu)
               (readBackNormal mot)
               (readBackNormal base)|]
readBackNeutral (NIndAbsurd neu mot) = 
    pure $ IndAbsurd (The Absurd !(readBackNeutral neu)) !(readBackNormal mot)
-- readBackNeutral arg = failure "badArg readBackNeutral"

-- p 37
unexpected : Ctx -> String -> Value -> M a


-- $$\def\U{{\cal U}}\def\LA\Leftarrow\def\RA\Rightarrow$$

check : Ctx -> Expr -> Ty -> M ()

synth : Ctx -> Expr -> M Ty
synth ctx (Var x) = do
    t <- lookupType ctx x
    pure t

-- $$\frac{\Gamma\vdash A\Leftarrow\U\quad\Gamma,x:A\vdash D\Leftarrow\U}{\Gamma\vdash(\Pi((x\,A)) D)\Rightarrow \U}$$
synth ctx (Pi x a b) = do
    check ctx a VU
    check (extendCtx ctx x !(eval (mkEnv ctx) a)) b VU
    pure VU

-- $$\frac{\Gamma\vdash rator\LA\U\quad\Gamma,x:A\vdashD\LA\U}{\Gamma\vdash(\Sigma((X\,A)) D)\RA\U}$$
synth ctx (App rator rand) = do
    VPi a b <- synth ctx rator | other => unexpected ctx "Not a Pi type" other
    check ctx rand a
    evalClosure b !(eval (mkEnv ctx) rand)

-- $$\frac{\Gamma\vdash A\LA\U\quad\Gamma,x:A\vdash D\LA\U}{\Gamma\vdash(\Sigma((x\,A))D)\RA\U}$$
synth ctx (Sigma x a b) = do
    check ctx a VU
    check (extendCtx ctx x !(eval (mkEnv ctx) a)) b VU
    pure VU

-- $$\frac{\Gamma\vdash e\RA(\Sigma((x\,A))D)}{\Gamma\vdash(\mathrm{car}e)\RA A}$$
synth ctx (Car e) = do
    VSigma aT dT <- synth ctx e | other => unexpected ctx "Not a sigma type" other
    pure aT

-- $$\frac{\Gamma\vdash e\RA(\Sigma((x\,A)) D)}{\Gamma\vdash(\mathop{cdr}e)\RA D[(\mathop{car}e)/x]}$$

synth ctx (Cdr e) = do
    VSigma aT dT <- synth ctx e | other => unexpected ctx "Not a sigma type" other
    evalClosure dT !(doCar !(eval (mkEnv ctx) e))

-- $$\frac{}{\Gamma\vdash\mathop{Nat}\RA\U}$$

synth ctx Nat = pure VU

-- $$\frac{}{}$$

synth ctx (IndNat tgt mot base step) = do
    VNat <- synth ctx tgt | other => unexpected ctx "not nat" other
    tgtV <- eval (mkEnv ctx) tgt
    motTy <- eval (ENV []) (Pi "x" Nat U)
    check ctx mot motTy 
    motV <- eval (mkEnv ctx) mot
    check ctx base !(doApply motV VZero)
    check ctx step !(indNatStepType motV)
    doApply motV tgtV

-- $$\frac{\Gamma\vdash A\LA\U\quad\Gamma\vdash from\LA A\quad \Gamma\vdash to\LA A}{\Gamma\vdash(=\,A\,from\,to)\RA\U}$$

synth ctx (Equal ty from to) = do
    check ctx ty VU
    tyV <- eval (mkEnv ctx) ty
    check ctx from tyV
    check ctx to tyV
    pure VU

-- $$\frac{}{}$$

synth ctx (Replace tgt mot base) = do
    VEq ty from to <- synth ctx tgt | t => unexpected ctx "Not an equality type" t
    motTy <-  eval (ENV [("ty",ty)]) (Pi "x" (Var "ty") U) 
    check ctx mot motTy
    motV <- eval (mkEnv ctx) mot
    doApply motV to

synth _ Trivial = pure VU
synth _ Absurd = pure VU
synth _ Atom = pure VU
synth _ U = pure VU

synth ctx (The ty expr) = do
    check ctx ty VU
    tyV <- eval (mkEnv ctx) ty
    check ctx expr tyV
    pure tyV

synth ctx other = failure "unable to synthesize type"


convert : Ctx -> Ty -> Value -> Value -> M ()
convert ctx t v1 v2 = do
    e1 <- readBackTyped ctx t v1
    e2 <- readBackTyped ctx t v2
    if aEquiv e1 e2
        then pure ()
        else failure "e1 and e2 are not same type"
    
-- p 40

-- $$\frac{\Gamma,x:A\vdash b\LA B}{\Gamma\vdash(\lambda(x)b)\LA(\Pi((x\,A))B)}$$

check ctx (Lambda x body) t = do
    let VPi a b = t | other => unexpected ctx "Not a Pi type" other
    xV <- evalClosure b (VNeutral a (NVar x))
    check (extendCtx ctx x a) body xV

check ctx (Cons a d) t = do
    let VSigma aT dT = t | other => unexpected ctx "Not a Sigma" other
    check ctx a aT
    aV <- eval (mkEnv ctx) a
    check ctx d !(evalClosure dT aV)

check ctx Zero t = case t of
    VNat => pure ()
    other => unexpected ctx "Type is not Nat" other

check ctx (Add1 n) t = do
    let VNat = t | other => unexpected ctx "Type is not Nat" other
    check ctx n VNat

check ctx Same t = do
    let VEq t from to = t | other => unexpected ctx "Type is not Equal" other
    convert ctx t from to

check ctx Sole VTrivial = pure ()
check ctx Sole other = unexpected ctx "Not Trivial" other

check ctx (Tick a) VAtom = pure ()
check ctx (Tick a) other = unexpected ctx "Not Atom" other

-- $$\frac{\Gamma\vdash e\RA t'\quad\Gamma\vdash t'\equiv t:\U}{\Gamma\vdash e\LA t}$$

check ctx other t = do
    t' <- synth ctx other
    convert ctx VU t' t



-- § 6.5.5 (p.44)

data Toplevel = Define Name Expr | Example Expr

data Output = ExampleOutput Expr
--Eq Show

toplevel : Ctx -> Toplevel -> M (List Output,Ctx)
toplevel ctx (Define x e) =
    case lookupType ctx x of
        Right _ => failure "The name \{show x} is already defined."
        Left _ => do
            t <- synth ctx e
            v <- eval (mkEnv ctx) e
            pure ([],define ctx x t v)
toplevel ctx (Example e) = do
    t <- synth ctx e
    v <- eval (mkEnv ctx) e
    e' <- readBackTyped ctx t v
    t' <- readBackTyped ctx VU t
    pure ([ExampleOutput (The t' e')], ctx)


-- so to wrap it in a repl

reserved : List String
reserved = ["def","zero","Nat","car","cdr","Sole","Some","Trivial","Same","U"]

parseName : Parser Name
parseName = do
    txt <- pack <$> [| letter :: many alphaNum |]
    spaces
    if elem txt reserved then fail "not ident \{txt}" else pure txt    

parseExpr : Parser Expr

parseLambda : Parser Expr
parseLambda = do
    token "λ"
    -- todo types?
    args <- some parseName
    token "."
    body <- parseExpr
    pure $ foldr Lambda body args


parseAExpr : Parser Expr
parseAExpr = parens parseExpr
    <|> Zero <$ token "zero"
    <|> Nat <$ token "Nat"
    <|> Trivial <$ token "Trivial"
    <|> Same <$ token "Some"
    <|> Sole <$ token "Sole"
    <|> Absurd <$ token "Absurd"
    <|> Atom <$ token "Atom"
    <|> U <$ token "U"
    <|> (Var <$> parseName)

parseApp : Parser Expr
parseApp = pure $ foldl App !parseAExpr !(many parseAExpr)

one : (Expr -> Expr) -> String -> Parser Expr
one a b = a <$ token b <*> parseAExpr


two : (Expr -> Expr -> a) -> String -> Parser a
two a b = a <$ token b <*> parseAExpr <*> parseAExpr


parseExpr = parseLambda --<|> parseRec 
    <|> one Add1 "add1"
    <|> two Cons "cons"
    <|> one Car "car"
    <|> one Cdr "cdr"
    <|> two IndNat "indNat" <*> parseAExpr <*> parseAExpr
    <|> two Equal "equal" <*> parseAExpr
    <|> two Replace "replace" <*> parseAExpr
    <|> two IndAbsurd "indAbsurd"
    <|> parseApp

parseDef : Parser Toplevel
parseDef = do
    token "let"
    name <- parseName
    args <- many parseName
    type <- token ":" *> parseExpr
    token "="
    body <- parseExpr
    let expr = foldr Lambda body args
    spaces
    pure $ Define name (The expr type)
    
parseTop : Parser Toplevel
parseTop = parseDef <|> Example <$> parseExpr


step' : Ctx -> String -> M (String,Ctx)
step' ctx txt = do
    (exp,_) <- parse parseTop txt | Left err => Left err
    (out,ctx) <- toplevel exp
    let foo = unlines $ map show out
    Right (foo, ctx)



step : Ctx -> String -> Maybe (String, Ctx)
step ctx txt = ?X



main : IO ()
main = replWith initCtx "> " step
