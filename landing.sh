set -eu
set -o pipefail

rm index.html

cat landing-top.html >> landing.html

find . -name "index.html" \
  | grep -v "master\|experimental" \
  | sed 's|\./\([^\/]*\)/index.html|\1|g' \
  | sort -r \
  | sed 's|^\(.*\)$|        <li><a href="\1">\1</a></li>|g' \
  >> landing.html

cat landing-bottom.html >> landing.html

mv landing.html index.html
