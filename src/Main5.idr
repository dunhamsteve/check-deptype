-- implementing-types-hs.pdf

-- Just kinda hacked section 4 stuff in, ignoring eval, and mutating the parser a bit.

import Data.String.Parser
import Data.String
import Data.List
import Data.List1
import Data.Either
import Data.Maybe
import Debug.Trace

dlog : Show a => a -> a
dlog a = trace (show a) a

data Name = NM String
Show Name where show (NM s) = s
Eq Name where (NM a) == (NM b) = a == b

data Ty
    = TNat
    | TArr Ty Ty
    -- | TVar Name

Show Ty where
    show TNat = "Nat"
    show (TArr a b) = case a of
        TArr _ _ => "(\{show a}) -> \{show b}"
        _ => "\{show a} -> \{show b}"
    -- show (TVar n) = show n

Eq Ty where
    TNat == TNat = True
    TArr a b == TArr c d = a == c && b == d
    _ == _ = False



data Expr 
    = Var Name
    | Lambda Name Expr
    | App Expr Expr
    | Zero
    | Add1 Expr
    | Rec Ty Expr Expr Expr
    | Ann Expr Ty

-- Notes: Add1 / Zero are constructors.  We've got some complexity with parens that probably just need showprec.. 

Show Expr where
    show (Var v) = show v
    -- TODO de-telescope
    show (Lambda v e) = go e [v]
        where
            go : Expr -> List Name -> String
            go (Lambda v e) args = go e (v :: args)
            go e args = "λ \{unwords $ map show $ reverse args} . \{show e}"
            
    show (App rator rand) = case rand of
        App _ _ => show rator ++ " (" ++ show rand ++ ")"
        -- constructor too
        Add1 _  => show rator ++ " (" ++ show rand ++ ")"
        _ => show rator ++ " " ++ show rand 
    
    show Zero = "zero"
    show (Add1 e) = case e of
        (Var x) => "add1 \{show e}"
        Zero => "add1 \{show e}"
        (Ann x y) => "add1 \{show e}"
        _ => "add1 (\{show e})"

    show (Ann e ty) = "(\{show e} : \{show ty})"
    show (Rec ty a b c) = "[rec \{show ty} \{show a} \{show b} \{show c}]"

data Env val = MkEnv (List (Name,val))

initEnv : Env a
initEnv = MkEnv []

showEnv : Show a => Env a -> String
showEnv (MkEnv es) = show es

Functor Env where
    map f (MkEnv es) = MkEnv (map (map f) es)

data Message = MSG String
Show Message where show (MSG msg) = msg

failure : String -> Either Message a
failure msg = Left (MSG msg)

lookupVar : Env a -> Name -> Either Message a
lookupVar (MkEnv []) (NM x) = failure "Not found: \{x}"
lookupVar (MkEnv ((y,v)::xs)) x =
    if x == y then Right v else lookupVar (MkEnv xs) x

extend : Env a -> Name -> a -> Env a
extend (MkEnv env) x v = MkEnv ((x,v) :: env)

mutual
    data Value
        = VZero
        | VAdd1 Value
        | VClosure (Env Value) Name Expr
        | VNeutral Ty Neutral

    Show Value where
        show (VClosure env n e) = assert_total $ "VClosure \{showEnv env} \{show n} \{show e}"
        show VZero = "Z"
        show (VAdd1 VZero) = "S Z"
        show (VAdd1 e) = "S (\{show e})"

    data Neutral
        = NVar Name
        | NApp Neutral Normal
        | NRec Ty Neutral Normal Normal

    Show Neutral where
        show (NVar n) = "NVar \{show n}"
        show (NApp n v) = "NApp \{show n} \{show v}"

    record Normal where
        constructor MkNormal
        type : Ty
        value : Value
    Show Normal where
        show (MkNormal t v) = "(\{show v} : \{show t})"
mutual
    doApply : Value -> Value -> Either Message Value
    doApply (VClosure env x body) arg = eval (extend env x arg) body
    doApply (VNeutral (TArr t1 t2) neu) arg = Right (VNeutral t2 (NApp neu (MkNormal t1 arg)))
    doApply (VNeutral t _) _ = failure "Expected arrow type, got: \{show t}"
    doApply x _ = failure "Tried to apply \{show x}"


    doRec : Ty -> Value -> Value -> Value -> Either Message Value
    doRec t VZero base step = pure base
    doRec t (VAdd1 n) base step =
        doApply !(doApply step n) !(doRec t n base step)
    doRec t (VNeutral TNat neu) base step =
        pure $ VNeutral t (NRec t neu
                            (MkNormal t base)
                            (MkNormal (TArr TNat (TArr t t)) step))
    doRec t foo base step = failure "doRec - not a Nat: \{show foo}"


    eval : Env Value -> Expr -> Either Message Value
    eval env (Var x) = lookupVar env x
    eval env (Lambda x body) = Right (VClosure env x body)
    eval env (App e f) = doApply !(eval env e) !(eval env f)
    eval env Zero = pure VZero
    eval env (Add1 n) = VAdd1 <$> eval env n
    eval env (Rec t tgt base step) = doRec t !(eval env tgt) !(eval env base) !(eval env step)
    eval env (Ann e t) = eval env e


freshen : List Name -> Name -> Name
freshen used x = if elem x used
    then freshen used (next x)
    else x
    where
        next : Name -> Name
        next (NM x) = NM (x ++ "'")

mutual
    readBackNormal : List Name -> Normal -> Either Message Expr
    readBackNormal used (MkNormal t v) = readBack used t v

    readBackNeutral : List Name -> Neutral -> Either Message Expr
    readBackNeutral used (NVar x) = pure $ Var x
    readBackNeutral used (NApp rator rand) =
        pure $ App  !(readBackNeutral used rator) !(readBackNormal used rand)
    readBackNeutral used (NRec t neu base step) =
        pure $ Rec t !(readBackNeutral used neu)
            !(readBackNormal used base)
            !(readBackNormal used step)

    readBack : List Name -> Ty -> Value -> Either Message Expr
    readBack used TNat VZero = pure Zero
    readBack used TNat (VAdd1 pred) = pure $ Add1 !(readBack used TNat pred)
    readBack used (TArr t1 t2) fun =
        let x = freshen used (argName fun)
            xVal = VNeutral t1 (NVar x)
        in Lambda x <$> readBack used t2 !(doApply fun xVal)
        where
            argName : Value -> Name
            argName (VClosure _ x _) = x
            argName _ = NM "x" -- ??
    readBack used t1 (VNeutral t2 neu) =
        if t1 == t2
            then readBackNeutral used neu
            else failure "readBackNeutral mismatch: \{show t1} != \{show t2}"
    readBack used TNat v@(VClosure _ _ _) = failure "readBack: not a Nat \{show v}"

normalize : Expr -> Either Message Expr
-- normalize expr = do
--     val <- eval initEnv expr
--     readBack Nil val

-- TODO - redo def syntax.

-- runProgram : List (Name, Expr) -> Expr -> Either Message Expr
-- runProgram defs expr = do
--     env <- addDefs initEnv defs
--     val <- eval env expr
--     readBack (map fst defs) val

reserved : List String
reserved = ["let","rec", "add1", "zero"]

parseName : Parser Name
parseName = do
    txt <- pack <$> [| letter :: many alphaNum |]
    spaces
    if txt `elem` reserved then fail "unexpected let" else pure $ NM txt

mutual
    parseLambda : Parser Expr
    parseLambda = do
        token "λ"
        args <- some parseName
        token "." 
        body <- parseExpr
        pure $ foldr Lambda body args

    parseRec : Parser Expr
    parseRec = do
        token "rec"
        token "["
        ty <- parseType
        token "]"
        a <- parseAExpr
        b <- parseAExpr
        c <- parseAExpr
        pure $ Rec ty a b c
    
    parseAExpr : Parser Expr
    parseAExpr = parens parseExpr 
                <|> Zero <$ token "zero" 
                <|> (Var <$> parseName)

    parseApp : Parser Expr
    parseApp = pure $ foldl App !parseAExpr !(many parseAExpr)

    parseExpr : Parser Expr
    parseExpr = parseLambda <|> parseRec 
                <|> (Add1 <$ token "add1" <*> parseAExpr )
                <|> parseApp

    parseType' : Parser Ty
    parseType' = (TNat <$ token "Nat") 
            --    <|> (TVar <$> parseName)
               <|> (parens parseType)

    parseType : Parser Ty
    parseType = do
        head <- parseType'
        case !(optional $ token "->") of
            Just _ => TArr head <$> parseType
            Nothing => pure head

    
        

parseDef : Parser (Name,Expr)
parseDef = do
    token "let"
    name <- parseName
    args <- many parseName
    type <- optional $ token ":" *> parseType
    token "="
    body <- parseExpr
    let expr = foldr Lambda body args
    spaces
    case type of
        Just ty => pure (name, Ann expr ty)
        Nothing => pure (name,expr)

parseDefs : Parser (List (Name,Expr))
parseDefs = many parseDef <* eos

Context = Env Ty

initCtx : Context
initCtx = initEnv

Defs = Env Normal

noDefs : Defs
noDefs = initEnv

defsToContext : Defs -> Context
defsToContext defs = map type defs

defsToEnv : Defs -> Env Value
defsToEnv defs = map value defs


mutual

    

    synth : Context -> Expr -> Either Message Ty

    -- \frac{}{\Gamma_1,x:t_1\Gamma_2\vdash x:t}
    synth ctx (Var x) = lookupVar ctx x

    -- \frac
    -- {\Gamma\vdash e_1 \Rightarrow A\to B\quad\Gamma\vdash e_2\Leftarrow A}
    -- {\Gamma\vdash e_1\,e_2\Rightarrow B}
    synth ctx (App rator rand) = do
        ty <- synth ctx rator
        case ty of
            TArr argT retT => do
                check ctx rand argT
                Right retT
            other => failure ("Not a function type: " ++ show other)
    
    synth ctx (Rec ty tgt base step) = do
        tgtT <- synth ctx tgt
        case tgtT of
            TNat => do
                check ctx base tgtT
                check ctx step (TArr TNat (TArr ty ty))
                Right ty
            other =>
                failure ("Not the type Nat: " ++ show other)
    -- \frac{\Gamma\vdash e\Leftarrow t_1}{\Gamma\vdash e\in t_1\Rightarrow t_!}
    synth ctx (Ann e t) = do
        check ctx e t
        Right t
    
    synth _ other =
        failure ("Can't find a type for " ++ show other ++ ". Try adding a type annotation.")


    check : Context -> Expr -> Ty -> Either Message ()
    check ctx (Lambda x body) t =
        case t of
            TArr arg ret => check (extend ctx x arg) body ret
            other => failure ("Lambda requires a function type, but got " ++ show other)

    check ctx Zero t =
        case t of
            TNat => Right ()
            other => failure ("Zero should be a Nat, but used where a " ++ show other ++ " was expected")

    check ctx (Add1 n) t =
        case t of
            TNat => check ctx n TNat
            other => failure ("Add1 should be a Nat, but used where a " ++ show other ++ " was expected")
    check ctx other t = do
        t' <- synth ctx other
        if t' == t
            then Right ()
            else failure "Expected \{show t} but got \{show t'}"

normWithDefs : Defs -> Expr -> Either Message Normal
normWithDefs defs e = 
    pure $ MkNormal !(synth (defsToContext defs) e) !(eval (defsToEnv defs) e)

addDefs : Defs -> List (Name,Expr) -> Either Message Defs
addDefs defs [] = Right defs
addDefs defs ((x,e)::rest) = do
    norm <- normWithDefs defs e
    addDefs (extend defs x norm) rest

definedNames : Defs -> List Name
definedNames (MkEnv defs) = map fst defs

parse' : Parser a -> String -> Either Message a
parse' p t = bimap MSG fst $ parse p t

normWithTestDefs : Expr -> Either Message Expr
normWithTestDefs e = do
    rawdefs <- parse' parseDefs $ unlines 
        [ "let two : Nat = add1 (add1 zero)"
        , "let three : Nat = add1 (add1 (add1 zero))"
        , "let plus n k : Nat -> Nat -> Nat = rec [Nat] n k (λ pred almostSum . add1 almostSum)"
        ]
    defs <- addDefs noDefs rawdefs
    norm <- normWithDefs defs e
    readBackNormal (definedNames defs) norm
    
runTest : String -> Either Message Expr
runTest test = normWithTestDefs !(parse' parseExpr test)

main : IO ()
main = do
    printLn $ runTest "plus"
    printLn $ runTest "plus three"
    printLn $ runTest "plus three two"
    
