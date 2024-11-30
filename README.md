# poST program collection
This repository contains a collection of poST programs with a set of requirements and generated verification conditions. The repository contains the following directories:

- Barrier--- the barrier control program
- Massage chair--- the massage chair control program
- RevolvingDoor--- the revolving door control program
- SmartLighting--- the smart lighting control program
- Turnstile--- the turnstile control program
- VendingMachine--- the vending machine control program
- WashingMachine--- the washing machine control program

Each directory has the following structure:
- File with extension .post— poST program
- File Requirements.thy— requirements in Isabelle/HOL
- Theory with the same name as the program file— Isabelle/HOL-theory with verification conditions
- File CommonExtraInv.thy— the requirement-independent extra invariant and proofs of verification conditions for it
- Files ExtraInv_Ri.thy— extra invariant for requirement Ri.
- Files Proofs_Ri.thy— proofs of verification conditions for the requirement Ri and the corresponding extra invariant.
