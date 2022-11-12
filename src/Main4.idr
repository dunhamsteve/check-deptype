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
    | TVar Name

Show Ty where
    show TNat = "Nat"
    show (TArr a b) = case a of
        TArr _ _ => "(\{show a}) -> \{show b}"
        _ => "\{show a} -> \{show b}"
    show (TVar n) = show n

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
        _ => show rator ++ " " ++ show rand 
    
    show Zero = "zero"
    show (Add1 e) = "add1 \{show e}"
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
        = VClosure (Env Value) Name Expr
        | VNeutral Neutral

    Show Value where
        show (VClosure env n e) = assert_total $ "VClosure \{showEnv env} \{show n} \{show e}"

    data Neutral
        = NVar Name
        | NApp Neutral Value

    Show Neutral where
        show (NVar n) = "NVar \{show n}"
        show (NApp n v) = "NApp \{show n} \{show v}"

mutual
    doApply : Value -> Value -> Either Message Value
    doApply (VClosure env x body) arg = eval (extend env x arg) body
    doApply (VNeutral neu) arg = Right (VNeutral (NApp neu arg))

    eval : Env Value -> Expr -> Either Message Value
    eval env (Var x) = lookupVar env x
    eval env (Lambda x body) = Right (VClosure env x body)
    eval env (App e f) = doApply !(eval env e) !(eval env f)

    -- REVIEW these are considered constructors now, and I think we can drop church encoding?
    eval env Zero = eval env (Var (NM "zero"))
    eval env (Add1 e) = eval env (App (Var (NM "add1")) e)
    eval _ _ = ?fixme


freshen : List Name -> Name -> Name
freshen used x = if elem x used
    then freshen used (next x)
    else x
    where
        next : Name -> Name
        next (NM x) = NM (x ++ "'")

readBack : List Name -> Value -> Either Message Expr
readBack used (VNeutral (NVar x)) = Right (Var x)
readBack used (VNeutral (NApp fun arg)) = do
    rator <- readBack used (VNeutral fun)
    rand <- readBack used arg
    Right (App rator rand)
readBack used fun@(VClosure _ x _) = do
    let x' = freshen used x
    bodyVal <- doApply fun (VNeutral (NVar x'))
    bodyExpr <- readBack (x' :: used) bodyVal
    Right (Lambda x' bodyExpr)
      
normalize : Expr -> Either Message Expr
normalize expr = do
    val <- eval initEnv expr
    readBack Nil val

-- TODO - redo def syntax.

addDefs : Env Value -> List (Name,Expr) -> Either Message (Env Value)
addDefs env ((x,e)::defs) = do
    v <- eval env e
    addDefs (extend env x v) defs
addDefs env [] = Right env

runProgram : List (Name, Expr) -> Expr -> Either Message Expr
runProgram defs expr = do
    env <- addDefs initEnv defs
    val <- eval env expr
    readBack (map fst defs) val

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
               <|> (TVar <$> parseName)
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

lam : String -> Expr -> Expr
lam n e = Lambda (NM n) e

var : String -> Expr
var n = Var (NM n)

churchDefs : List (Name,Expr)

toChurch : Int -> {default (var "zero") acc : Expr} ->  Expr
toChurch 0 = acc
toChurch n = toChurch (n - 1) {acc = App (var "add1") acc}
    -- if n <= 0
    -- then var "zero"
    -- else App (var "add1") (toChurch (n - 1))


stuff : List String
stuff = 
    [ "let zero f x = x"
    , "let add1 n f x = f (n f x)"
    , "let add j k f x = j f (k f x)"
    , "let foo x = a b c"
    ]


Context = Env Ty

initCtx : Context
initCtx = initEnv



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

addTDefs : Context -> List (Name,Expr) -> Either Message Context
addTDefs ctx [] = Right ctx
addTDefs ctx ((x,e)::defs) = do
        t <- synth ctx e
        addTDefs (extend ctx x t) defs


parseStuff : String -> List (Name,Expr)
parseStuff stuff =
    fromMaybe [] $ map fst $ getRight $ dlog $ parse parseDefs stuff
    -- let Right (defs,_) = parse parseDefs stuff | _ => []
    -- in defs


pExpr : String -> Either Message Expr
pExpr = bimap MSG fst .  parse parseExpr


test : Either Message (Ty,Ty)
test = do
    let defs = dlog $ parseStuff $ unlines $
            [ "let two : Nat = add1 (add1 zero)"
            , "let three : Nat = add1 (add1 (add1 zero))"
            , "let plus n k : Nat -> Nat -> Nat = rec [Nat] n k (λ pred almostSum . add1 almostSum)"
            ]
    ctx <- addTDefs initCtx defs
    t1 <- synth ctx =<< pExpr "plus three"
    t2 <- synth ctx =<< pExpr "plus three two"
    Right (t1,t2)

main : IO ()
main = do
    let Right (churchDefs,_) = parse parseDefs (unlines stuff) | Left err => printLn err
    printLn churchDefs
    putStrLn "---"
    printLn $ runProgram churchDefs (toChurch 2)
    putStrLn "---"
    printLn $ runProgram churchDefs (App (App (var "add") (toChurch 2)) (toChurch 3))
    
