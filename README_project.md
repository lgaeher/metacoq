
### Guardedness and Positivity checker

## Installation 

1. Setup a clean opam switch.
  ```
    opam switch create guardedness-mc 4.09.1+flambda 
    eval $(opam env)
  ```

2. Install Coq
    ```
      opam install coq=8.11.2
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
* `Inductives.v` contains preliminaries for inductives.
* `positivitychecker.v` contains an implementation of the positivity checker.
* `guardchecker.v` contains an implementation of the guardedness checker.
* `plugin.v` is the derived checker plugin in the template monad.
* `examples.v` contains some examples and explanations.
