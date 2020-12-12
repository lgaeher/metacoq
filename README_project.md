
### Guardedness checker

## Installation 

1. Setup a clean opam switch.
  ```
    opam switch create guardedness-mc 4.09.1+flambda 
    eval $(opam env)
  ```

2. The quoting of recursive trees relies on a fork of Coq.

  * Clone the repo and switch to the 8.11 branch.
    ```
      git clone git@github.com:lgaeher/coq.git coq-guardedness 
      cd coq-guardedness
      git checkout v8.11 
    ```
  * Install `conf-findutils` and `num`.
    ```
     opam repo add coq-released https://coq.inria.fr/opam/released   
     opam install conf-findutils num 
    ```

  * 
    Configure with enabled dynamic linking. Please use as prefix the opam switch you just created, e.g.
    ```
      ./configure -prefix /home/[user]/.opam/guardedness-mc -natdynlink yes
    ```

  * Make and make install
    ```
      make -j8
      make install
    ```

  * Fake the installation of Coq so that opam is happy.
    ```
      opam install --fake coq=8.11.2
      opam pin add coq 8.11.2
    ```

3. Install the MetaCoq fork.
  * Install equations.
      ```
      opam install coq-equations 
      ```
  
  * Clone the repo.
      ```
        cd ../
        git clone https://github.com/lgaeher/metacoq metacoq-guarded
        cd metacoq-guarded
      ```
  
  * Build MetaCoq. (we need the checker and template-coq plugins)
    ```
      ./configure.sh
      cd template-coq
      make -j8
      make install
      cd ../checker
      make -j8
      make install
      cd ..
    ```

  * Build the guardedness checker. 
    ``` 
      cd guarded
    ```
  
    You will now have to manually change the path to the checker and template-coq plugins in the `_CoqProject`, depending on where your opam switch is.
    Then:
    ```
      make -j4
      make doc
    ```

    The `html` directory contains coqdocs after building.

## Overview of the files in metacoq/guarded:
* `Except.v` and `Trace.v` are monads for exception handling and debugging
* `Inductives.v` is the main implementation of the checker.
* `plugin.v` is the derived checker plugin in the template monad.
* `examples.v` contains some examples and explanations.
