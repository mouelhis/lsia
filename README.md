# Language for describing and checking Semantical Interface Automata (Ph.D. work)

The **lSIA tool**, built upon the Language for describing and checking **Semantical Interface Automata**, provides an environment for specifying and verifying semantical interface automata. This tool enables the construction of compositions involving compatible semantic interface automata, with a focus on verifying the semantic compatibility of shared actions. Leveraging the CVC3 satisfiability solver, it ensures rigorous checks of semantic compatibility. The specifications of semantic interface automata are seamlessly translated into TLA+ for safety verification through model-checking techniques. This versatile tool offers a concise and efficient way to address compatibility concerns at different levels, including signature, semantics, and protocol (see [Ref]).

![Local Image](./diagramme_lsia.png)

[Ref] Mouelhi, Sebti. Contributions à la Vérification de la Sûreté de l'Assemblage et à l'Adaptation de Composants Réutilisables. *Ph.D. Thesis*, Université de Franche-Comté, 2011 (French manuscript).
