#!/bin/bash
# Script para verificar Bishop.java com OpenJML

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
    bash scripts/filter_output.sh "${CLASS_NAME}" || true

echo ""
echo "[$STEP/$TOTAL_STEPS] ✅ Verificação concluída!"
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📈 Estatísticas:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Conta erros e avisos
ERRORS=$(grep -c "error:" /tmp/jml_output_${CLASS_NAME}.log 2>/dev/null || echo "0")
WARNINGS=$(grep -c "warning:" /tmp/jml_output_${CLASS_NAME}.log 2>/dev/null || echo "0")
VERIFY_ISSUES=$(grep -c "verify:" /tmp/jml_output_${CLASS_NAME}.log 2>/dev/null || echo "0")

echo "  🔴 Erros:     $ERRORS"
echo "  🟡 Avisos:    $WARNINGS"
echo "  🔵 Verificações: $VERIFY_ISSUES"
echo ""

if [ "$ERRORS" -eq "0" ] && [ "$VERIFY_ISSUES" -eq "0" ]; then
    echo "✨ ${CLASS_NAME}.java: VERIFICAÇÃO BEM-SUCEDIDA!"
else
    echo "⚠️  ${CLASS_NAME}.java: Encontrados problemas (veja acima)"
fi

echo ""
echo "=========================================="
echo "🏁 Fim da verificação de ${CLASS_NAME}.java"
echo "=========================================="
echo ""
