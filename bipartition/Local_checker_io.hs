import Local_checker
import System.Environment

boolEq :: Local_checker.Bool -> Local_checker.Bool -> Prelude.Bool
boolEq Local_checker.True Local_checker.True = Prelude.True
boolEq Local_checker.False Local_checker.False = Prelude.True
boolEq _ _ = Prelude.False

int_to_nat :: Integer -> Nat
int_to_nat 0 = O
int_to_nat x = S (int_to_nat (x - 1))

int_to_cid :: Integer -> Component
int_to_cid 0 = O
int_to_cid x = S (int_to_nat (x - 1))

bool_to_bool :: Prelude.Bool -> Local_checker.Bool
bool_to_bool Prelude.True = Local_checker.True
bool_to_bool Prelude.False = Local_checker.False

list_to_List :: [Component] -> List Component
list_to_List [] = Nil
list_to_List (hd : rest) = Local_checker.Cons hd (list_to_List rest)

single_nld_to_single_nld :: (Integer, Integer, Integer) -> (Prod (Prod Component Component) Nat)
single_nld_to_single_nld (n, l, d) = Pair (Pair (int_to_cid n) (int_to_cid l)) (int_to_nat d)

nlds_to_nld :: [(Integer, Integer, Integer)] -> List (Prod (Prod Component Component) Nat)
nlds_to_nld [] = Nil
nlds_to_nld (hd : rest) = Local_checker.Cons (single_nld_to_single_nld hd) (nlds_to_nld rest)

main :: IO()
main = do
  (ids:nis:ls:ps:ds:nlds:lbs:gocs:[]) <- getArgs -- IO [String]
  let id = int_to_cid (read ids :: Integer)
  let l = int_to_cid (read ls :: Integer)
  let p = int_to_cid (read ps :: Integer)
  let d = int_to_nat (read ds :: Integer)
  let lb = bool_to_bool (read lbs :: Prelude.Bool)
  let goc = bool_to_bool (read gocs :: Prelude.Bool)
  let ni = list_to_List (map int_to_cid (read nis :: [Integer]))
  let nld = nlds_to_nld (read nlds :: [(Integer, Integer, Integer)])
  putStr (if (boolEq Local_checker.True (local_checker id ni l p d nld lb goc))
    then "true"
    else "false")
