Parameter sort : Set.
Parameter axiom : sort -> sort -> Prop.
Parameter rule : sort -> sort -> sort -> Prop.

Parameter star : sort.

Definition size_sort (s:sort) := 1.

Parameter sort_regularity : forall s1, exists s2, axiom s1 s2.
