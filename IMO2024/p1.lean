import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Have

open scoped BigOperators

/--
求所有实数 $\alpha$ 使得对于每个正整数 $n$，都有整数

$$
\lfloor \alpha\rfloor + \lfloor2\alpha\rfloor + \cdots + \lfloor n\alpha\rfloor
$$

是 $n$ 的倍数。

（注意：$\lfloor z\rfloor$ 表示小于或等于 $z$ 的最大整数。
例如，$\lfloor-\pi\rfloor = -4$ 和 $\lfloor2\rfloor = \lfloor2.9\rfloor = 2$ 。）

解答：$\alpha$ 是一个偶数。
-/
theorem imo_2024_p1 :
   /-
   左侧集合：α 是实数且满足：对任意自然数 n，当 n > 0 时，整数 n 整除 ⌊i * α⌋ 的和，其中 i 取 1 到 n。
   右侧集合：α 是实数且满足：存在整数 k，使得 k 是偶数且 α = k。
   -/
   {(α : ℝ) | ∀ (n : ℕ), 0 < n → (n : ℤ) ∣ (∑ i in Finset.Icc 1 n, ⌊i * α⌋)}
   = {α : ℝ | ∃ k : ℤ, Even k ∧ α = k} := by
   /- a = b ↔ a ⊆ b ∧ b ⊆ a 分两侧证明 -/
  rw [Set.Subset.antisymm_iff]
  /- 根据集合定义，证明左侧元素 x 落在右侧 -/
  rw [Set.subset_def ]
  /- 引入一个变量 `l` 用于证明的第二部分（难的方向），即 `2l = ⌊α⌋ + ⌊2α⌋`
     通过可整除性条件取 n = 2 得出。 -/
  exists λx L=>(L 2 zero_lt_two).rec λl Y=>?_
  use λy . x => y.rec λS p=>?_
  · /- 我们首先证明形如 `2k` 的每个 `α` 都满足条件。
       在这种情况下，和简化为 `kn(n+1)`，
       这显然是 `n` 的倍数。 -/
    simp_all[λL:ℕ=>(by norm_num[Int.floor_eq_iff]:⌊(L:ℝ)*S⌋=L* S )]
    rw[p.2,Int.dvd_iff_emod_eq_zero,Nat.lt_iff_add_one_le,<-Finset.sum_mul,←Nat.cast_sum, S.even_iff, ←Nat.Ico_succ_right,@ .((( Finset.sum_Ico_eq_sum_range))),Finset.sum_add_distrib ]at*
    simp_all[Finset.sum_range_id]
    exact dvd_trans ⟨2+((_:ℕ)-1),by linarith[((‹ℕ›:Int)*(‹Nat›-1)).ediv_mul_cancel$ Int.prime_two.dvd_mul.2<|by ·omega]⟩ ↑↑(mul_dvd_mul_left @_ (p))
  /- 现在我们证明逆命题，即左边的每个 `α` 都是一个偶数。
     我们声称，对于所有这样的 `α` 和 $n \in \mathbb{N}$，
     有 `⌊(n+1)*α⌋ = ⌊α⌋ + 2n(l-⌊α⌋)`。 -/
  suffices : ∀ (n : ℕ),⌊(n+1)*x⌋ =⌊ x⌋+2 * ↑ (n : ℕ) * (l-(⌊(x)⌋))
  · /- 假设该主张成立，看看它是如何足以完成我们的证明的。 -/
    zify[mul_comm,Int.floor_eq_iff] at this
    -- 我们将证明 `α = 2(l-⌊α⌋)`，这显然是偶数。
    use(l-⌊x⌋)*2
    norm_num
    -- 为了做到这一点，足以证明 `α ≤ 2(l-⌊α⌋)` 和 `α ≥ 2(l-⌊α⌋)`。
    apply@le_antisymm
    /- 要证明第一个不等式，注意如果 `α > 2(l-⌊α⌋)`，则存在正整数
       `N > 0`，使得 `N ≥ 1/(α - 2(l -⌊α⌋))`。
       基于我们的假设主张（n = N），我们有
       `⌊α⌋ + 2(l-⌊α⌋)N + 1 > (N+1)α`，即
       `⌊α⌋ + (2(l-⌊α⌋) - α)N + 1 > α`，
       这意味着 `⌊α⌋ > α`，矛盾。 -/
    use not_lt.1 (by cases exists_nat_ge (1/(x-_)) with|_ N =>nlinarith[ one_div_mul_cancel $ sub_ne_zero.2 ·.ne',9,Int.floor_le x, this N])
   /- 类似地，如果 `α < 2(l-⌊α⌋)` 那么我们可以找到一个正的自然数 `N`，
      使得 `N ≥ 1/(2(l-⌊α⌋) - α)`。
      基于我们假设的主张（n = N），我们有
      `(N+1)α ≥ ⌊α⌋ + 2(l-⌊α⌋)N`，即
      `α ≥ ⌊α⌋ + (2(l-⌊α⌋) - α)N`，
      这意味着 `a ≥ ⌊α⌋ + 1`，矛盾。 -/
    use not_lt.1 (by cases exists_nat_ge (1/_:ℝ)with|_ A=>nlinarith[Int.lt_floor_add_one x,one_div_mul_cancel$ sub_ne_zero.2 ·.ne',this A])
  /- 现在所有要做的就是证明我们的主张
     `⌊(n + 1)α⌋ = ⌊α⌋ + 2n(l - ⌊α⌋)`。 -/
  intro
  -- 我们通过对 `n` 进行强归纳法来推理。
  induction‹_› using@Nat.strongInductionOn
  -- 根据我们对 `α` 的假设，我们知道 `(n+1) | ∑_{i=1}^(n+1) ⌊iα⌋`
  specialize L$ ‹_›+1
  simp_all[add_comm,mul_assoc,Int.floor_eq_iff,<-Nat.Ico_succ_right, add_mul,(Finset.range_succ), Finset.sum_Ico_eq_sum_range]
  revert‹ℕ›
  /- 因此，存在 `c` 使得
     `(n+1)*c = ∑_{i=1}^{n+1} ⌊iα⌋ = ⌊nα+α⌋ + ∑_{i=1}^{n} ⌊iα⌋`。 -/
  rintro A B@c
  simp_all[ Finset.mem_range.mp _,←eq_sub_iff_add_eq',Int.floor_eq_iff]
  /- 根据归纳假设，
     `∑_{i=0}^{(n-1)}, ⌊α+iα⌋ = ∑_{i=0}^{(n-1)}, ⌊α⌋+2*i*(l-⌊α⌋)`。 -/
  suffices:∑d in .range A,⌊x+d*x⌋=∑Q in .range A,(⌊x⌋+2*(Q * (l-.floor x)))
  · suffices:∑d in ( .range A),(((d)):ℤ) =A * ( A-1)/2
    · have:(A : ℤ) * (A-1)%2=0
      · cases@Int.emod_two_eq A with|_ B=>norm_num[B,Int.sub_emod,Int.mul_emod]
      norm_num at*
      norm_num[ Finset.sum_add_distrib,<-Finset.sum_mul, ←Finset.mul_sum _ _] at*
      rw[eq_sub_iff_add_eq]at*
      /- 结合
         `∑_{i=0}^{n-1},⌊iα+α⌋ = (n+1)c - ⌊nα+α⌋`，
         我们有 `⌊nα+α⌋= (n+1)c - n⌊α⌋ - n(n-1)(l-⌊α⌋)` 所以
         `⌊nα+α⌋ ≥ (n+1)c - n⌊α⌋ - n(n-1)(l-⌊α⌋)`
         和
         `⌊nα+α⌋ < (n+1)c - n⌊α⌋ - n(n-1)(l-⌊α⌋) + 1`。
         另外，因为 `2*l = ⌊α⌋ + ⌊2α⌋`，我们有
         `2α + ⌊α⌋ - 1 < 2*l ≤ 2α + ⌊α⌋。` -/
      zify[←mul_assoc, this,←eq_sub_iff_add_eq',‹_ =(@ _) /@_›,Int.floor_eq_iff] at *
      zify[*]at*
      -- 我们现在将展示 `c =n*(l-⌊α⌋)+⌊α⌋`。
      cases S5:lt_or_ge c (A*(l-⌊x⌋)+⌊x⌋+1)
      · simp_all
        have:(c+1:ℝ)<=A*(l-⌊x⌋)+⌊x⌋+1:=by norm_cast
        simp_all
        cases this.eq_or_lt
        · /- 因为如果 `c=n*(l-⌊α⌋)+⌊α⌋ `，那么
             ```
             ⌊(n+1)α⌋ = (n+1)c - n⌊α⌋ - n(n-1)(l-⌊α⌋)
             = (n+1)(n(l-⌊α⌋) + ⌊α⌋) - n⌊α⌋ - n(n-1)(l-⌊α⌋)
             = 2n(l-⌊α⌋) + ⌊α⌋
             ```
             按照期望。 -/
           repeat use by nlinarith
        /- 现在，我们通过矛盾证明 `c = n*(l-⌊α⌋) + ⌊α⌋`，
           分成两种情况。首先假设 `c ≤ n(l-⌊α⌋)+⌊α⌋-1`。
           ```
           (n+1)α < (n+1)c - n⌊α⌋ - n(n-1)(l-⌊α⌋) + 1
           ≤ (n+1)(n(l-⌊α⌋) + ⌊α⌋ - 1) - n⌊α⌋ - n(n-1)(l-⌊α⌋) + 1
           = 2n(l-⌊α⌋) + ⌊α⌋ - n
           = 2ln - 2n⌊α⌋ + ⌊α⌋ - n
           ≤ (2α+⌊α⌋)n - 2n⌊α⌋ + ⌊α⌋ - n
           = nα + n(α-⌊α⌋-1) + ⌊α⌋
           n + α。
           ```
           矛盾。 -/
        nlinarith[(by norm_cast at* :(A*(l -⌊x⌋):ℝ)+⌊(x)⌋ >=(c)+01),9,Int.add_emod ↑5,Int.floor_le (@x : ℝ),Int.lt_floor_add_one (x:)]
      /- 接下来，假设 `c ≥ n(l-⌊α⌋)+⌊α⌋+1`。
         ```
         (n+1)α ≥ (n+1)c - n⌊α⌋ - n(n-1)(l-⌊α⌋)
         ≥ (n+1)(n(l-⌊α⌋) + ⌊α⌋ + 1) - n⌊α⌋ - n(n-1)(l-⌊α⌋)
         = 2n(l-⌊α⌋) + ⌊α⌋ + n + 1
         = 2ln - 2n⌊α⌋ + ⌊α⌋ + n + 1
         > (2α+⌊α⌋-1)n - 2n⌊α⌋ + ⌊α⌋ + n + 1
         = nα + n(α-⌊α⌋) + ⌊α⌋ + 1
         > n + α
         ```
         矛盾。 -/
      simp_all
      nlinarith[(by norm_cast:(c:ℝ)>=A*(l-⌊_⌋)+⌊_⌋+1),Int.floor_le x,Int.lt_floor_add_one x]
    rw [←Nat.cast_sum, mul_sub, Finset.sum_range_id]
    cases A with|_=>norm_num[mul_add]
  use Finset.sum_congr rfl<|by simp_all[add_comm,Int.floor_eq_iff]

#print axioms imo_2024_p1
