#!/bin/bash
# Script para verificar Bishop.java com OpenJML

# Obtém o diretório do script
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

CLASS_NAME="Bishop"
echo "=========================================="
echo "🔍 Verificando ${CLASS_NAME}.java"
echo "=========================================="
echo ""

# Contador de progresso
STEP=1
TOTAL_STEPS=3

echo "[$STEP/$TOTAL_STEPS] 📦 Carregando dependências..."
STEP=$((STEP + 1))

echo "[$STEP/$TOTAL_STEPS] ⚙️  Executando OpenJML..."
STEP=$((STEP + 1))

# Executa OpenJML e mostra progresso
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 Resultados da Verificação:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

cd "$PROJECT_ROOT"

openjml --esc --progress -classpath src/main/java \
    src/main/java/boardgame/Position.java \
    src/main/java/boardgame/Board.java \
    src/main/java/boardgame/BoardException.java \
    src/main/java/boardgame/Piece.java \
    src/main/java/chess/Color.java \
    src/main/java/chess/ChessPosition.java \
    src/main/java/chess/ChessException.java \
    src/main/java/chess/ChessPiece.java \
    src/main/java/chess/pieces/Bishop.java 2>&1 | \
    tee /tmp/jml_output_${CLASS_NAME}.log | \
    bash "$SCRIPT_DIR/filter_output.sh" "${CLASS_NAME}" || true

echo ""
echo "[$STEP/$TOTAL_STEPS] ✅ Verificação concluída!"
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📈 Estatísticas:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Conta erros e avisos
ERRORS=$(grep -c "error:" /tmp/jml_output_${CLASS_NAME}.log 2>/dev/null | head -1 || echo "0")
WARNINGS=$(grep -c "warning:" /tmp/jml_output_${CLASS_NAME}.log 2>/dev/null | head -1 || echo "0")
VERIFY_ISSUES=$(grep -c "verify:" /tmp/jml_output_${CLASS_NAME}.log 2>/dev/null | head -1 || echo "0")

# Remove espaços e quebras de linha
ERRORS=$(echo "$ERRORS" | tr -d ' \n')
WARNINGS=$(echo "$WARNINGS" | tr -d ' \n')
VERIFY_ISSUES=$(echo "$VERIFY_ISSUES" | tr -d ' \n')

echo "  🔴 Erros:     ${ERRORS:-0}"
echo "  🟡 Avisos:    ${WARNINGS:-0}"
echo "  🔵 Verificações: ${VERIFY_ISSUES:-0}"
echo ""

if [ "${ERRORS:-0}" -eq "0" ] && [ "${VERIFY_ISSUES:-0}" -eq "0" ]; then
    echo "✨ ${CLASS_NAME}.java: VERIFICAÇÃO BEM-SUCEDIDA!"
else
    echo "⚠️  ${CLASS_NAME}.java: Encontrados problemas (veja acima)"
fi

echo ""
echo "=========================================="
echo "🏁 Fim da verificação de ${CLASS_NAME}.java"
echo "=========================================="
echo ""
