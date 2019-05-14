set -eu
set -o pipefail
for i in $( find src -name "*.agda" \
          | sed 's/src\/\(.*\)\.agda/\1/' \
          | sed 's/\//\./g' \
          | sort \
          ); do
  echo "import $i" >> index.agda;
  if [[ ! $i == *Unsafe \
     && ! $i == Reflection \
     && ! $i == IO* \
     && ! $i == *TrustMe ]]; then echo "import $i" >> safe.agda; fi
done
