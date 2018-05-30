Contributing to the library
===========================

Thank you for your interest in contributing to the Agda standard library. Hopefully this guide should make it easy to do so! Feel free to ask any questions on the Agda mailing list.

How to make changes
-------------------

### Fork and download the repository

1. Create a fork by clicking `Fork` button at the top right of the [repository](https://github.com/agda/agda-stdlib).

2. If you are on a Mac, make sure that your git options has `autocrlf` set to `input`.  This can be done by executing
   ```
   git config --global core.autocrlf input
   ```
   If you are on Windows, make sure that your editor can deal with Unix format files.

3. On the command line, and in a suitable folder, download your fork by running the command
   ```
   git clone https://github.com/USER_NAME/agda-stdlib agda-stdlib-fork
   ```

   where `USER_NAME` is your Git username. The folder `agda-stdlib-fork` should now contain a copy of the standard library.

4. Enter the folder `agda-stdlib-fork` and choose the correct branch of the library to make your changes on by running the
   command
   ```
   git checkout X
   ```
   where `X` should be `master` if your changes are compatible with the current released version of Agda, and `experimental`
   if your changes require the development version of Agda.

### Make your changes

5. Make your proposed changes. Please try to obey existing conventions in the library.
   See `agda-stdlib-fork/notes/style-guide.md` for a selection of the most important ones.

6. Document your changes in `agda-stdlib-fork/CHANGELOG.md`.

7. Ensure your changes are compatible with the rest of the library by running the commands
   ```
   make clean
   make test
   ```
   inside the `agda-stdlib-fork` folder. Continue to correct any bugs thrown up until the tests are passed.

   Your proposed changes MUST pass these tests. Note that the tests require the use of a tool called
   `fix-agda-whitespace`. See the instructions at the end of this file for how to install this.

### Upload your changes

8. Use the `git add` command to add the files you have changed to your proposed commit.

9. Run the command:
   ```
   git commit
   ```
   and enter a meaningful description for your changes.

10. Upload your changes to your fork by running the command:
   ```
   git push
   ```
11. Go to your fork on Github at `https://github.com/USER_NAME/agda-stdlib` and click the green `Compare & pull request` button to open a pull request.

12. The standard library maintainers will then be made aware of your requested changes and should be in touch soon.

Installing `fix-agda-whitespace`
--------------------------------

This tool is kept in the main agda repository. It can be installed by following these instructions:
   ```
   git clone https://github.com/agda/agda
   cd agda/src/fix-agda-whitespace
   cabal install
   ```

