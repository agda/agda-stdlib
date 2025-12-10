#!/bin/sh

set -eu

isDebugMode() {
  ! [ -z ${DEBUG-} ]
}

if ! [ -z ${SHELL_DEBUG-} ]; then
  set -x
fi

throwError() {
  echo "\033[91m✗\033[0m $1." >&2
  exit 1
}

logHappy() {
  echo "\033[32m✔\033[0m $1"
}

logWarning() {
  echo "\033[93m⚠\033[0m $1"
}

checkDependency () {
  if ! [ -x "$(command -v $1)" ]; then
    throwError "Missing dependency: I could not find the executable '$1'"
  elif isDebugMode; then
    logHappy "Found '$1'"
  fi
}

checkDependency "grep"
checkDependency "head"
checkDependency "mkdir"
checkDependency "sed"
checkDependency "tar"
checkDependency "touch"
checkDependency "wget"

# Pick the Agda executable to analyse
# unless the caller has specified one
if [ -z ${AGDA_EXEC-} ]; then
  read -p "What's the name of your Agda executable (default: agda)? " AGDA_EXEC
  if [ -z "$AGDA_EXEC" ]; then
    AGDA_EXEC=agda
  fi
fi

# Double check that the command exists
if ! [ -x "$(command -v $AGDA_EXEC)" ]; then
  throwError "'$AGDA_EXEC' is not a valid executable"
fi

logHappy "Agda executable: $AGDA_EXEC"

# Ask the executable for its version number
# unless the caller has specified one
if [ -z ${AGDA_VERSION-} ]; then
  # There is a more recent "--numeric-version" option but old
  # versions of Agda do not implement it!
  AGDA_VERSION=$($AGDA_EXEC --version | head -n 1 | sed "s/^[a-zA-Z ]*\(2[0-9.]*\)\(-.*\)*$/\1/")
fi

# Double check that the version number is correct
if ! echo "$AGDA_VERSION" | grep -Eq "^2(\.[0-9]+)+$"; then
  throwError "'$AGDA_VERSION' is not a valid version number"
fi

logHappy "Agda version number: $AGDA_VERSION"

# Pick the install directory
# unless the caller has specified one
if [ -z ${AGDA_DIR-} ]; then
  AGDA_DIR=$($AGDA_EXEC --print-agda-app-dir | head -n 1 || true)
  if echo "$AGDA_DIR" | grep -Eq "^Error.*$"; then
    AGDA_DIR="$HOME/.agda"
  fi
  read -p "Where do you want to install the library (default: $AGDA_DIR)? " AGDA_DIR_OVERWRITE
  if ! [ -z "$AGDA_DIR_OVERWRITE" ]; then
    AGDA_DIR="$AGDA_DIR_OVERWRITE"
  fi
fi

logHappy "Agda directory: $AGDA_DIR"

if [ -z ${STDLIB_VERSION-} ]; then
  case "$AGDA_VERSION" in
    "2.8.0")   STDLIB_VERSION="2.3" ;;
    "2.7.0.1") STDLIB_VERSION="2.3" ;;
    "2.7.0")   STDLIB_VERSION="2.2" ;;
    "2.6.4.3") STDLIB_VERSION="2.1" ;;
    "2.6.4.2") STDLIB_VERSION="2.0" ;;
    "2.6.4.2") STDLIB_VERSION="2.0" ;;
    "2.6.4.1") STDLIB_VERSION="2.0" ;;
    "2.6.4")   STDLIB_VERSION="2.0" ;;
    "2.6.3")   STDLIB_VERSION="1.7.3" ;;
    "2.6.2.2") STDLIB_VERSION="1.7.1" ;;
    "2.6.2.1") STDLIB_VERSION="1.7.1" ;;
    "2.6.1")   STDLIB_VERSION="1.7.1" ;;
    *)         STDLIB_VERSION="experimental" ;;
  esac
fi

logHappy "Standard library version: $STDLIB_VERSION"

case "$STDLIB_VERSION" in
  "master")       STDLIB_TAG="refs/heads/master" ;;
  "experimental") STDLIB_TAG="refs/heads/experimental" ;;
  *)              STDLIB_TAG="v$STDLIB_VERSION" ;;
esac

# Setting up the Agda install directory
mkdir -p "$AGDA_DIR"
cd "$AGDA_DIR"
mkdir -p logs

# Downloading and extracting the standard library
STDLIB_DIR_NAME="agda-stdlib-$STDLIB_VERSION"
STDLIB_TARBALL_NAME="/tmp/$STDLIB_DIR_NAME.tar.gz"
STDLIB_TARBALL_URL="https://github.com/agda/agda-stdlib/archive/$STDLIB_TAG.tar.gz"
wget -O "$STDLIB_TARBALL_NAME" "$STDLIB_TARBALL_URL" -o logs/wget

logHappy "Successfully downloaded the standard library"

if [ -d "$STDLIB_DIR_NAME" ]; then
  logWarning "The directory $AGDA_DIR/$STDLIB_DIR_NAME already exists."
  while true; do
    read -p "Do you want to overwrite it? (yN) " DIR_OVERWRITE
    DIR_OVERWRITE=${DIR_OVERWRITE:-n}
    case "$DIR_OVERWRITE" in
      [yY]*) DIR_OVERWRITE="y"; break;;
      [nN]*) DIR_OVERWRITE="n"; break;;
      *) echo "Please answer y or n.";;
    esac
  done
  if [ "$DIR_OVERWRITE" = "y" ]; then
    rm -rf "$STDLIB_DIR_NAME"
    tar -zxvf "$STDLIB_TARBALL_NAME" > logs/tar
  fi
else
  tar -zxvf "$STDLIB_TARBALL_NAME" > logs/tar
fi

# Adding the standard library to the list of installed and default libraries
STDLIB_PATH="$AGDA_DIR/agda-stdlib-$STDLIB_VERSION/standard-library.agda-lib"
AGDA_LIBRARIES_FILE="libraries-$AGDA_VERSION"

touch "$AGDA_LIBRARIES_FILE"
if ! grep -Eq "$STDLIB_PATH" "$AGDA_LIBRARIES_FILE"; then
  echo "$STDLIB_PATH" >> "$AGDA_LIBRARIES_FILE"
fi

touch "defaults-$AGDA_VERSION"
if ! grep -Eq "^standard-library$" "defaults-$AGDA_VERSION"; then
  echo "standard-library" >> "defaults-$AGDA_VERSION"
fi

logHappy "Successfully installed the standard library"
