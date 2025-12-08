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
# linhas relevantes da classe (arquivo, verify, error).
# OCULTA warnings - mostra apenas erros e verificações
# IGNORA erros de toString() e hashCode() relacionados a Object.jml
awk -v cls="$CLASS_NAME" '
    /Progress|Proving|[0-9]+%|\[[0-9]+\/[0-9]+\]/ { print "  " $0; next }
    /error:/ && !/Object\.jml:(72|219)/ { print "  " $0; next }
    /verify:/ && index($0, cls ".java") > 0 && !/Object\.jml:(72|219)/ { print "  " $0; next }
    index($0, cls ".java") > 0 && /verify:/ && !/Object\.jml:(72|219)/ { print "  " $0; next }
    /Object\.jml:(72|219)/ { next }  # Ignora completamente linhas com Object.jml:72 ou :219
'

