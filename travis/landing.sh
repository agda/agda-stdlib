set -eu
set -o pipefail

find html/ -name "index.html" \
  | grep -v "master\|experimental" \
  | sort \
  | sed 's|html/\([^\/]*\)/index.html|  <li><a href="\1">\1</a></li>|g' \
  >> landing.html

echo "</ul>" >> landing.html

mv landing.html html/index.html
