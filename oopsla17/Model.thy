theory Model imports Main begin

(* Points in the domain *)
datatype domain = Fin int | Bot | Top 
  
fun domainEq :: "domain \<Rightarrow> domain \<Rightarrow> bool" where
  "domainEq Bot Bot = True" |
  "domainEq Top Top = True" |
  "domainEq (Fin n) (Fin m) = (n = m)" |
  (* expanded catch all to remove duplicate rewrite warnings*) 
  "domainEq Bot y     = False  " |
  "domainEq Top y     = False" |
  "domainEq (Fin n) y  = False"
  
(* Intervals on the domain *)
type_synonym interval = "(domain * domain)"

inductive contiguous1 :: "interval \<Rightarrow> interval \<Rightarrow> bool" where
   "(m \<equiv> (n+1)) \<Longrightarrow> contiguous1 (i, Fin n) (Fin m, j)"

fun coalesce1 :: "interval \<Rightarrow> interval \<Rightarrow> interval option" where
   "coalesce1 (i, Fin n) (Fin m, j) = (if (m = (n+1)) then Some (i, j) else None)" |
   "coalesce1 x y = None"

(* Hyperectangles as a cartesian product of intervals *)
type_synonym hrect = "interval list"

fun intervalEq :: "interval \<Rightarrow> interval \<Rightarrow> bool" where
  "intervalEq (a, b) (c, d) = ((domainEq a c) \<and> (domainEq b d))"
  
fun hrectEq :: "hrect \<Rightarrow> hrect \<Rightarrow> bool" where
  "hrectEq [] [] = True" |
  "hrectEq [] _ = False" |
  "hrectEq _ [] = False" |
  "hrectEq (x # xs) (y # ys) = ((intervalEq x y) \<and> (hrectEq xs ys))"

(* set model *)

inductive intervalMod :: "int \<Rightarrow> interval \<Rightarrow> bool" where
  intervalI: "intervalMod n (Bot, Top)"
| interval2I: "n \<le> b \<and> a \<le> n \<Longrightarrow> (intervalMod n ((Fin a), (Fin b)))"
  
end
  