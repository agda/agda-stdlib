Installation instructions
=========================

Note: the full story on installing Agda libraries can be found at [readthedocs](http://agda.readthedocs.io/en/latest/tools/package-system.html).

Use version v2.0 of the standard library with Agda 2.6.4 or 2.6.4.1.

1. Navigate to a suitable directory `$HERE` (replace appropriately) where
   you would like to install the library.

2. Download the tarball of v2.0 of the standard library. This can either be
   done manually by visiting the Github repository for the library, or via the
   command line as follows:
   ```
   wget -O agda-stdlib.tar https://github.com/agda/agda-stdlib/archive/v2.0.tar.gz
   ```
   Note that you can replace `wget` with other popular tools such as `curl` and that
   you can replace `2.0` with any other version of the library you desire.

3. Extract the standard library from the tarball. Again this can either be
   done manually or via the command line as follows:
   ```
   tar -zxvf agda-stdlib.tar
   ```

4. [ OPTIONAL ] If using [cabal](https://www.haskell.org/cabal/) then run
   the commands to install via cabal:
   ```
   cd agda-stdlib-2.0
   cabal install
   ```

5. Locate the file `$HOME/.agda/libraries` where `$HOME` on Ubuntu/MacOS
   is an environment variable that points to your home directory. The
   value of the environment variable can be found by running `echo $HOME`.

   Note that the `.agda` directory and the `libraries` file within it,
   may not exist and you may have to create them.

6. Register the standard library with Agda's package system by adding
   the following line to `$HOME/.agda/libraries`:
   ```
   $HERE/agda-stdlib-2.0/standard-library.agda-lib
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
