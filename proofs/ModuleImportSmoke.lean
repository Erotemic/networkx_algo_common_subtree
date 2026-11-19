module

import SubtreeProofs

/-!
# Public API import smoke test

This file deliberately imports only the umbrella module. Compile it with
`lake env lean ModuleImportSmoke.lean` from the `proofs/` directory to verify
that downstream modules can access the declarations through public imports.
-/

#check SubtreeProofs.Paper2004.OrderedTree
#check SubtreeProofs.Paper2004.OrderedTree.ContractStep
#check SubtreeProofs.Paper2004.OrderedTree.encodeDyck_semilength
#check SubtreeProofs.Paper2004.OrderedTree.decodeDyck_encodeDyck
#check SubtreeProofs.Paper2004.OrderedTree.embeds_encodeDyck
#check SubtreeProofs.Paper2004.OrderedTree.dyckEmbeds_decodeDyck
#check SubtreeProofs.Paper2004.OrderedTree.embeds_iff_dyckEmbeds
