# Scripts de Verificação OpenJML

Este diretório contém scripts individuais para verificar cada classe do projeto com OpenJML.

## Estrutura

Cada script verifica uma classe específica, incluindo todas as suas dependências necessárias, e filtra a saída para mostrar apenas os resultados relevantes da classe em questão.

## Scripts Disponíveis

### Classes Básicas (boardgame)
- `verify_Position.sh` - Verifica Position.java
- `verify_BoardException.sh` - Verifica BoardException.java
- `verify_Board.sh` - Verifica Board.java
- `verify_Piece.sh` - Verifica Piece.java

### Classes de Xadrez (chess)
- `verify_Color.sh` - Verifica Color.java
- `verify_ChessException.sh` - Verifica ChessException.java
- `verify_ChessPosition.sh` - Verifica ChessPosition.java
- `verify_ChessPiece.sh` - Verifica ChessPiece.java
- `verify_ChessMatch.sh` - Verifica ChessMatch.java

### Classes de Peças (chess.pieces)
- `verify_Bishop.sh` - Verifica Bishop.java
- `verify_Queen.sh` - Verifica Queen.java
- `verify_Knight.sh` - Verifica Knight.java
- `verify_Rook.sh` - Verifica Rook.java
- `verify_King.sh` - Verifica King.java
- `verify_Pawn.sh` - Verifica Pawn.java

### Classes de Aplicação (app)
- `verify_UI.sh` - Verifica UI.java
- `verify_Main.sh` - Verifica Main.java

### Script Master
- `verify_all.sh` - Executa todos os scripts de verificação em sequência

## Como Usar

### No Linux/Mac:

1. Dar permissão de execução aos scripts:
```bash
chmod +x scripts/*.sh
```

2. Executar um script individual:
```bash
./scripts/verify_Bishop.sh
```

3. Executar todos os scripts:
```bash
./scripts/verify_all.sh
```

### No Windows (usando Git Bash ou WSL):

1. Executar um script individual:
```bash
bash scripts/verify_Bishop.sh
```

2. Executar todos os scripts:
```bash
bash scripts/verify_all.sh
```

## Formato da Saída

Cada script:
1. Mostra um cabeçalho indicando qual classe está sendo verificada
2. Executa o OpenJML com `--esc --progress` e todas as dependências necessárias
3. Filtra a saída para mostrar apenas:
   - Linhas relacionadas ao arquivo da classe (ex: `Bishop.java`)
   - Mensagens de verificação (`verify:`)
   - Erros (`error:`)
   - Avisos (`warning:`)
4. Mostra um rodapé indicando o fim da verificação

## Exemplo de Saída

```
=== Verificando Bishop.java ===

Bishop.java:22: verify: The prover cannot establish an assertion...
Bishop.java:20: verify: Associated declaration...

=== Fim da verificação de Bishop.java ===
```

## Notas

- Os scripts assumem que você está executando a partir da raiz do projeto
- O OpenJML deve estar instalado e no PATH
- As dependências são automaticamente incluídas em cada script
- A saída é filtrada para focar apenas na classe sendo verificada

