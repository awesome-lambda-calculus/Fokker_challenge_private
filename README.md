# Fokker_challenge

The currently known smallest one-point basis for untyped lambda calculus (in terms of **Fokker size**) is **α** , discovered by John Tromp.

```
α = λλλ2 0 (1 (λ1))
B = λλλ2 (1 0) = α(α(α(α(α α) α))(α α) α)(α(α(α α)))
C = λλλ2 0 1 = α(α α α(α α α)(α α)(α α)) α α
K = λλ1 = α α(α(α α) α α α) α(α α)
W = λλ1 0 0 = α α(α(α(α α) α))
I = λ0 = α(α(α(α α) α))(α(α α) α)
F = λλ0 = α α α(α(α α)(α α)(α α)) α
S = λλλ (2 0) (1 0) = B (B W) (B B C) = ...
```

The Fokker size of a closed term is the number of abstractions and applications it contains when written.

```
def fokker_size : (Term String) -> Nat
| bvar _ => 0
| fvar _ => 0
| abs t => 1 + fokker_size t
| app t1 t2 => 1 + fokker_size t1 + fokker_size t2
```


Our goal:
- Verify α is smallest basis Or
- Find the smallest basis

We use lean4 to formalize that all smaller closed lambda term can't be basis.

Our proof is based on [cslib](https://github.com/leanprover/cslib).

Currently we focus on normal forms.
When all normal forms are checked, we will turn to non normal forms.

## Waht we have Done

We have formalize two simple deciders, which have proven 1421 terms could not be basis.

## What we are going to do 
There are still 1264 terms undecided:

```
$ lake exe fokker_challenge

1264 undecided
```

We might prove them one by one, or discover new deciders.

See issues to startup

## Next step

1. Verify "Two vars are not enough", which will cover 78 terms
2. Filter terms always terminate
3. Filter terms always diverge
4. Not sure


## Undecide problems

1. How to name theorem which verify term is not basis: Godel encoding ?

## How to deal with undecided terms

Some might diverge, we haven't proved. 

### Ai usage

This project is quite suitable for AI-Driven Autonomous Proof.

### Reference
- https://esolangs.org/wiki/Closed_lambda_term
- https://github.com/tromp/AIT/blob/master/Bases.lhs

