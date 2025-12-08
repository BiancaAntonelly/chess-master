#!/bin/bash
# Função auxiliar para filtrar a saída do OpenJML mantendo o progresso
# Uso: filter_output <nome_da_classe>
# Exemplo: filter_output "Bishop"

CLASS_NAME="$1"

if [ -z "$CLASS_NAME" ]; then
    echo "Erro: Nome da classe não fornecido"
    exit 1
fi

# Mantém linhas de progresso (contendo %, Progress, Proving, [n/m]) e
# linhas relevantes da classe (arquivo, verify, error, warning).
# Indenta a saída para melhor leitura.
awk -v cls="$CLASS_NAME" '
    /Progress|Proving|[0-9]+%|\[[0-9]+\/[0-9]+\]/ { print "  " $0; next }
    index($0, cls ".java") > 0 || /verify:|error:|warning:/ { print "  " $0; next }
'

