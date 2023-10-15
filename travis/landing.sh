set -eu
set -o pipefail

rm html/index.html

cat landing-top.html >> landing.html

find html/ -name "index.html" \
  | grep -v "master\|experimental" \
  | sed 's|html/\([^\/]*\)/index.html|\1|g' \
  | sort -r \
  | sed 's|^\(.*\)$|        <li><a href="\1">\1</a></li>|g' \
  >> landing.html

cat landing-bottom.html >> landing.html

mv landing.html html/index.html
mv agda-logo.svg html/
