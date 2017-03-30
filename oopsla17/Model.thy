theory Model imports Main begin

(* Points in the domain *)
datatype domain = Fin int | Bot | Top 
  
fun domainEq :: "domain \<Rightarrow> domain \<Rightarrow> bool" where
  "domainEq Bot Bot = True" |
  "domainEq Top Top = True" |
  "domainEq (Fin n) (Fin m) = (n = m)" |
  (* expanded catch all to remove duplicate rewrite warnings*) 
  "domainEq Bot y     = False" |
  "domainEq Top y     = False" |
  "domainEq (Fin n) y  = False"
  
type_synonym holeFlag = "bool"
  
(* Intervals on the domain *)
type_synonym interval = "(domain * domain * holeFlag)"

 (*
inductive contiguous1 :: "interval \<Rightarrow> interval \<Rightarrow> bool" where
   "((m \<equiv> (n+1)) \<and> (p \<or> q)) \<Longrightarrow> contiguous1 (i, Fin n, p) (Fin m, j, q)"
*)
  
fun coalesce1 :: "interval \<Rightarrow> interval \<Rightarrow> interval option" where
   "coalesce1 (i, Fin n, p) (Fin m, j, q) = (if (m = (n+1)) then Some (i, j, p \<or> q) else None)" |
   "coalesce1 x y = None"

(* Hyperectangles as a cartesian product of intervals *)
type_synonym hrect = "interval list"

fun intervalEq :: "interval \<Rightarrow> interval \<Rightarrow> bool" where
  "intervalEq (a, b, p) (c, d, q) = ((domainEq a c) \<and> (domainEq b d) \<and> (p = q))"
  
 
fun hrectEq :: "hrect \<Rightarrow> hrect \<Rightarrow> bool" where
  "hrectEq [] [] = True" |
  "hrectEq [] _ = False" |
  "hrectEq _ [] = False" |
  "hrectEq (x # xs) (y # ys) = ((intervalEq x y) \<and> (hrectEq xs ys))"

(* set model *)

inductive intervalModel :: "int \<Rightarrow> interval \<Rightarrow> bool" where
  intervalWild: "intervalModel n (Bot, Top, True)"
| intervalWildHole: "n \<noteq> 0 \<Longrightarrow> intervalModel n (Bot, Top, False)"
| intervalFin: "n \<le> b \<and> a \<le> n \<Longrightarrow> (intervalModel n (Fin a, Fin b, True))"
| intervalFinHole: "n \<le> b \<and> a \<le> n \<and> n \<noteq> 0 \<Longrightarrow> (intervalModel n (Fin a, Fin b, False))"
  
end
  