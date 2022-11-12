theory Peano
  imports Main
begin

section \<open>Natural Numbers\<close>

datatype nat = Zero | Suc nat

fun add :: "nat => nat => nat" where
  "add Zero m = m" |
  "add (Suc n) m = Suc (add n m)"

lemma neutral[simp]: "add m Zero = m"
  apply (induction m)
  apply auto
  done

lemma suc_commutation[simp]: "add m (Suc n) = Suc (add m n)"
  apply (induction m)
   apply auto
  done

lemma commutation[simp]: "add m n = add n m"
  apply (induction m)
   apply auto
  done

lemma preassociation: "nat.Suc (add n (add k m)) = add n (add m (nat.Suc k))"
  apply (induction n)
   apply auto
  done

lemma association[simp]: "add k (add m n) = add (add k m) n"
  apply (induction k)
   apply (auto simp:preassociation)
  done

fun double :: "nat \<Rightarrow> nat" where
  "double Zero = Zero" |
  "double (Suc n) = add (double n) (Suc (Suc Zero))"

lemma double_def: "double n = add n n"
  apply (induction n)
  apply auto

end 
