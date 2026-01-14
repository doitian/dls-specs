------------------------------ MODULE knapsack ------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSetsExt
CONSTANTS Items

Capacity == 7
ItemParams == [size: 2..4, value: 0..5]
ItemSets == [Items -> ItemParams]

KnapsackSize(sack, itemset) ==
  LET size_for(item) == itemset[item].size * sack[item]
  IN FoldSet(LAMBDA item, acc: size_for(item) + acc, 0, Items)

ValidKnapsacks(itemset) ==
  {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

\* Oh hey duplicate code
KnapsackValue(sack, itemset) ==
  LET value_for(item) == itemset[item].value * sack[item]
  IN FoldSet(LAMBDA item, acc: value_for(item) + acc, 0, Items)

BestKnapsack(itemset) ==
  LET all == ValidKnapsacks(itemset)
  IN CHOOSE best \in all:
    \A worse \in all \ {best}:
      KnapsackValue(best, itemset) > KnapsackValue(worse, itemset)

BestKnapsacksOne(itemset) ==
  LET all == ValidKnapsacks(itemset)
  IN CHOOSE all_the_best \in SUBSET all:
    /\ \E good \in all_the_best:
         /\ \A other \in all_the_best:
              KnapsackValue(good, itemset) = KnapsackValue(other, itemset)
         /\ \A worse \in all \ all_the_best:
              KnapsackValue(good, itemset) > KnapsackValue(worse, itemset)


BestKnapsacksTwo(itemset) ==
  LET
    all == ValidKnapsacks(itemset)
    best == CHOOSE best \in all:
      \A worse \in all \ {best}:
        KnapsackValue(best, itemset) >= KnapsackValue(worse, itemset)
    value_of_best == KnapsackValue(best, itemset)
  IN
    {k \in all: value_of_best = KnapsackValue(k, itemset)}
-----------------------------------------------------------------------------
VARIABLES itemset

Init == /\ itemset \in ItemSets
        /\ Assert(BestKnapsacksTwo(itemset) \subseteq ValidKnapsacks(itemset), "Best knapsacks found")

Next == UNCHANGED itemset

Spec == Init /\ [][Next]_itemset
-----------------------------------------------------------------------------
Symmetry == Permutations(Items)
=============================================================================
