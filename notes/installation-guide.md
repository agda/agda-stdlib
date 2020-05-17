Installation instructions
=========================

Use version v1.3 of the standard library with Agda 2.6.1.

1. Navigate to a suitable directory `$HERE` (replace appropriately) where
   you would like to install the library.

2. Download the tarball of v1.3 of the standard library. This can either be
   done manually by visiting the Github repository for the library, or via the
   command line as follows:
   ```
   wget -O agda-stdlib.tar https://github.com/agda/agda-stdlib/archive/v1.3.tar.gz
   ```
   Note that you can replace `wget` with other popular tools such as `curl` and that
   you can replace `1.3` with any other version of the library you desire.

3. Extract the standard library from the tarball. Again this can either be
   done manually or via the command line as follows:
   ```
   tar -zxvf agda-stdlib.tar
   ```

4. [ OPTIONAL ] If using [cabal](https://www.haskell.org/cabal/) then run
   the commands to install via cabal:
   ```
   cd agda-stdlib-1.3
   cabal install
   ```

5. Register the standard library with Agda's package system by adding
   the following line to `$HOME/.agda/libraries`:
   ```
   $HERE/agda-stdlib-1.3/standard-library.agda-lib
   ```

Now, the standard library is ready to be used either:

- in your project `$PROJECT`, by creating a file
  `$PROJECT.agda-lib` in the project's root containing:
  ```
  depend: standard-library
  include: $DIRS
  ```
  where `$DIRS` is a list of directories where Agda
  searches for modules, for instance `.` (just the project's root).

- in all your projects, by adding the following line to
  `$HOME/.agda/defaults`
  ```
  standard-library
  ```

Find the [full story at readthedocs](http://agda.readthedocs.io/en/latest/tools/package-system.html) about installing Agda libraries.
