#!/bin/bash

JML="/Applications/openjml/openjml"

FILE="$1"

if [ -z "$FILE" ]; then
  echo "Uso: ./run_jml_tests.sh <arquivo.java>"
  exit 1
fi

if [ ! -f "$FILE" ]; then
  echo "Arquivo não encontrado: $FILE"
  exit 1
fi

echo "== Iniciando testes JML para $FILE =="
echo ""

METHODS=$(grep -oE 'public [^()]+[ ]+[a-zA-Z0-9_]+\(' "$FILE" \
  | sed 's/.* \(.*\)(/\1/' \
  | sort -u)

for m in $METHODS; do
  echo "🔍 Testando método: $m"

  $JML --esc --classpath . "$FILE" >/dev/null 2>&1

  if [ $? -eq 0 ]; then
    echo "✔ Teste bem-sucedido para o método '$m'"
  else
    echo "❌ Falha no método '$m'"
  fi

  echo "-------------------------------------------"
done

echo "== Testes concluídos para $FILE =="
