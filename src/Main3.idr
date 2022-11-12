-- implementing-types-hs.pdf

import Data.String.Parser
import Data.String
import Data.List
import Data.Either
import Data.Maybe

data Name = NM String
Show Name where show (NM s) = s
Eq Name where (NM a) == (NM b) = a == b

data Expr 
    = Var Name
    | Lambda Name Expr
    | App Expr Expr

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


foo : String
foo = "let zero = λ f x . x\nlet add1 = λ n f x . f (n f x)\nlet add = λ j k f x . j f (k f x)\n"

parseName : Parser Name
parseName = do
    txt <- pack <$> [| letter :: many alphaNum |]
    spaces
    if txt == "let" then fail "unexpected let" else pure $ NM txt

mutual
    parseLambda : Parser Expr
    parseLambda = do
        token "λ"
        args <- some parseName
        token "." 
        body <- parseExpr
        pure $ foldr Lambda body args

    parseAExpr : Parser Expr
    parseAExpr = parens parseExpr <|> (Var <$> parseName)

    parseApp : Parser Expr
    parseApp = pure $ foldl App !parseAExpr !(many parseAExpr)

    parseExpr : Parser Expr
    parseExpr = parseLambda <|> parseApp

parseDef : Parser (Name,Expr)
parseDef = do
    name <- token "let" *> parseName
    token "="
    expr <- parseExpr
    spaces
    pure (name,expr)

parseDefs : Parser (List (Name,Expr))
parseDefs = many parseDef <* eos

lam : String -> Expr -> Expr
lam n e = Lambda (NM n) e

var : String -> Expr
var n = Var (NM n)

churchDefs : List (Name,Expr)

toChurch : Int -> Expr
toChurch n = if n <=0
    then var "zero"
    else App (var "add1") (toChurch (n - 1))


stuff : List String
stuff = 
    [ "let zero = λ f x . x"
    , "let add1 = λ n f x . f (n f x)"
    , "let add  = λ j k f x . j f (k f x)"
    , "let foo = λ x . (a b c)"
    ]

main : IO ()
main = do
    let Right (churchDefs,_) = parse parseDefs (unlines stuff) | Left err => printLn err
    printLn churchDefs
    putStrLn "---"
    printLn $ runProgram churchDefs (toChurch 2)
    putStrLn "---"
    printLn $ runProgram churchDefs (App (App (var "add") (toChurch 2)) (toChurch 3))
    
