set -eu
set -o pipefail

rm html/index.html

cat landing-top.html >> landing.html

find html/ -name "index.html" \
  | grep -v "master\|experimental" \
  | sort -r \
  | sed 's|html/\([^\/]*\)/index.html|      <li><a href="\1">\1</a></li>|g' \
  >> landing.html

cat landing-bottom.html >> landing.html

mv landing.html html/index.html
