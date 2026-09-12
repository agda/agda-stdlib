* Added a folder "Logic" in src. This provides a formalization of several 
substructural logics based on chapter 2 of Greg Restall's "An Introduction to 
Substructural Logics". This provides a framework for anyone wanting to study
substructural logics. 

The underlying definition of "logic" shared by all substructural logics is given
in src/Logic/Logic.agda. This definition includes several features:
1. A language, which is the set of possible propositions within the logic
2. A set of structures, which are collections of premises, and a map from the
language to structures
3. A consecution relation "⊢" that determines what propositions can be deduced 
from what collections of premises
4. A context function from structures to structuress; we will see that this allows for
more expressive power for structural rules. 
5. A semicolon function for making a structure from a pair of structures; this is our
first example of a *punctuation mark*, which allow us to inductively create
more complex structures. Punctuation marks get their significance from how they 
interact with connectives in the language.
6. A conective ⇒ representing implication in our language.
The body of the definition provides rules governing the interplay between the 
semicolon and the implication arrow.


--describe overall design
--bundle lang and structure into a record
--figure out why I didn't pass smaller logical forms as parameters


