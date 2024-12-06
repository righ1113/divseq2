# divseq2
割数列を用いたコラッツ予想の証明Ⅱ  
前作からの変更点：十分条件を改良しました  

<br />
<br />
<br />

# 変更履歴
24/12/06 Lean 4 4.15.0-rc1 に更新  
23/03/03 完成しました  
23/01/14 説明を書きました  
23/01/10 ひとまず出来た  
23/01/07 init  

# コラッツ予想とは
コラッツの問題は、「任意の正の整数 n をとり、  
  
- n が偶数の場合、n を 2 で割る  
- n が奇数の場合、n に 3 をかけて 1 を足す  
  
という操作を繰り返すと、どうなるか」というものである。  
「どんな初期値から始めても、有限回の操作のうちに必ず 1 に到達する(そして 1→4→2→1 というループに入る)」という主張が、コラッツの予想である。   

（Wikipediaより）  

# 割数列とは
コラッツ操作で2で割った回数を並べます。  
これを割数列と名付けます。  
例えば9の場合は、コラッツ列は  
9,28,14,7,22,11,34,17,52,26,13,40,20,10,5,16,8,4,2,1  
ですから割数列は  
[2,1,1,2,3,4]  
となります。

初期値が3の倍数の割数列を完全割数列と名付けます。  
9[2,1,1,2,3,4]は完全割数列です。  
7[1,1,2,3,4]はふつうの割数列です。  
　  

# Explanation of source code
See [1] for theoretical background.  

## Divseq2/Basic.lean
### parity and mod3
I use this when divided case.  
### allDivSeq
I have to connect `allDivSeq` and `ExtsLimited`, but I haven't started yet.  
But it doesn't affect the proof.  
### ExtsLimited
Each term represents the inverse of the extended star conversion.  
### SingleLimited
My theorem proving was that `is01(single 9)`, `is10(single 3)` could not be a constructor. `axiom`.  

## Divseq2.lean
### singleToExts
Sufficient condition.  
It uses 3 lemmas, and 6 axioms.  
There are two stages of assigning constructors to arguments.  
[241206] I recently proved 6 axioms.  
### makeLimitedDivSeq
It uses 12 lemmas.  
### LimitedDivSeq
This is the final theorem.  
Passing `makeLimitedDivSeq` to the well-founded function.  

## axiom
Seen from the human, every axiom proposition is self-evident.  

# Reference
[1] Furuta, Masashi. "Proof of Collatz Conjecture Using Division Sequence." Advances in Pure Mathematics 12.2 (2022): 96-108. DOI: 10.4236/apm.2022.122009  

<br />
<br />
<br />
