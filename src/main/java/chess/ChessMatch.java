package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;
import chess.pieces.*;

import java.util.ArrayList;
import java.util.List;

public class ChessMatch {

    protected Board board;

    private int turn;

    private Color currentPlayer;

    private boolean check;

    private boolean checkMate;

    private ChessPiece enPassantVulnerable;

    private ChessPiece promoted;

    private final List<Piece> piecesOnTheBoard;

    private final List<Piece> capturedPieces;

    public ChessMatch() {
        board = new Board(8, 8);
        turn = 1;
        currentPlayer = Color.WHITE;
        check = false;
        checkMate = false;
        enPassantVulnerable = null;
        promoted = null;
        piecesOnTheBoard = new ArrayList<>();
        capturedPieces = new ArrayList<>();
        initialSetup();
    }

    public ChessPiece[][] getPieces() {
        final int rows = board.getRows();
        final int cols = board.getCols();

        ChessPiece[][] mat = new ChessPiece[rows][];

        for (int i = 0; i < rows; i++) {
            ChessPiece[] rowArray = new ChessPiece[cols];
            mat[i] = rowArray;

            for (int j = 0; j < cols; j++) {
                Piece p = board.piece(i, j);

                if (p != null && p instanceof ChessPiece c) {
                    rowArray[j] = c;
                }
            }
        }

        return mat;
    }

    public int getTurn() {
        return turn;
    }

    public Color getCurrentPlayer() {
        return currentPlayer;
    }

    public boolean getCheck() {
        return check;
    }

    public boolean getNotCheckMate() {
        return !checkMate;
    }

    public boolean isCheckMate() {
        return checkMate;
    }

    public ChessPiece getEnPassantVulnerable() {
        return enPassantVulnerable;
    }

    public ChessPiece getPromoted() {
        return promoted;
    }

    public boolean[][] possibleMoves(ChessPosition sourcePos) {
        Position position = sourcePos.toPosition();
        validateSourcePosition(position);
        return board.piece(position).possibleMoves();
    }

    public ChessPiece performChessMove(ChessPosition sourcePos,
            ChessPosition targetPos) {
        Position source = sourcePos.toPosition();
        Position target = targetPos.toPosition();
        validateSourcePosition(source);
        validateTargetPosition(source, target);
        Piece captured = makeMove(source, target);

        if (testCheck(currentPlayer)) {
            undoMove(source, target, captured);
            throw new ChessException("Você não pode se colocar em xeque.");
        }
        ChessPiece moved = (ChessPiece) board.piece(target);

        // Promoção
        promoted = null;
        if (moved instanceof Pawn) {
            if ((moved.getColor() == Color.WHITE && target.getRow() == 0)
                    || (moved.getColor() == Color.BLACK && target.getRow() == 7)) {
                promoted = (ChessPiece) board.piece(target);
                promoted = replacePromotedPiece("Q");
            }
        }

        check = testCheck(opponent(currentPlayer));
        if (testCheckMate(opponent(currentPlayer))) {
            checkMate = true;
        } else {
            nextTurn();
        }

        // En Passant
        if (moved instanceof Pawn &&
                (target.getRow() == source.getRow() - 2 || target.getRow() == source.getRow() + 2)) {
            enPassantVulnerable = moved;
        } else {
            enPassantVulnerable = null;
        }

        return (ChessPiece) captured;
    }

    public ChessPiece replacePromotedPiece(String type) {
        if (promoted == null) {
            throw new IllegalStateException("Não há peça para ser promovida");
        }
        if (!type.equals("B") && !type.equals("N") && !type.equals("R") && !type.equals("Q")) {
            return promoted;
        }

        Position pos = promoted.getChessPosition().toPosition();
        Piece p = board.removePiece(pos);
        piecesOnTheBoard.remove(p);

        ChessPiece newPiece = newPiece(type, promoted.getColor());
        board.placePiece(newPiece, pos);
        piecesOnTheBoard.add(newPiece);
        promoted = newPiece;
        return newPiece;
    }

    private ChessPiece newPiece(String type, Color color) {
        if (type.equals("B")) {
            return new Bishop(board, color);
        } else if (type.equals("N")) {
            return new Knight(board, color);
        } else if (type.equals("Q")) {
            return new Queen(board, color);
        } else {
            return new Rook(board, color);
        }
    }

    private Piece makeMove(Position source, Position target) {
        ChessPiece p = (ChessPiece) board.removePiece(source);
        p.increaseMoveCount();
        Piece captured = board.removePiece(target);
        board.placePiece(p, target);

        if (captured != null) {
            piecesOnTheBoard.remove(captured);
            capturedPieces.add(captured);
        }
        // Roque pequeno (kingside castling)
        if (p instanceof King && target.getCol() == source.getCol() + 2) {
            Position sourceT = new Position(source.getRow(), source.getCol() + 3);
            Position targetT = new Position(source.getRow(), source.getCol() + 1);
            ChessPiece rook = (ChessPiece) board.removePiece(sourceT);
            board.placePiece(rook, targetT);
            rook.increaseMoveCount();
        }
        // Roque grande (queenside castling)
        if (p instanceof King && target.getCol() == source.getCol() - 2) {
            Position sourceT = new Position(source.getRow(), source.getCol() - 4);
            Position targetT = new Position(source.getRow(), source.getCol() - 1);
            ChessPiece rook = (ChessPiece) board.removePiece(sourceT);
            board.placePiece(rook, targetT);
            rook.increaseMoveCount();
        }
        // En Passant
        if (p instanceof Pawn) {
            if (source.getCol() != target.getCol() && captured == null) {
                Position pawnPosition = new Position(
                        p.getColor() == Color.WHITE ? target.getRow() + 1 : target.getRow() - 1,
                        target.getCol());
                captured = board.removePiece(pawnPosition);
                capturedPieces.add(captured);
                piecesOnTheBoard.remove(captured);
            }
        }

        return captured;
    }

    private void undoMove(Position source, Position target, Piece captured) {
        ChessPiece p = (ChessPiece) board.removePiece(target);
        p.decreaseMoveCount();
        board.placePiece(p, source);

        if (captured != null) {
            board.placePiece(captured, target);
        }
        // Roque pequeno (kingside castling)
        if (p instanceof King && target.getCol() == source.getCol() + 2) {
            Position sourceT = new Position(source.getRow(), source.getCol() + 3);
            Position targetT = new Position(source.getRow(), source.getCol() + 1);
            ChessPiece rook = (ChessPiece) board.removePiece(targetT);
            board.placePiece(rook, sourceT);
            rook.decreaseMoveCount();
        }
        // Roque grande (queenside castling)
        if (p instanceof King && target.getCol() == source.getCol() - 2) {
            Position sourceT = new Position(source.getRow(), source.getCol() - 4);
            Position targetT = new Position(source.getRow(), source.getCol() - 1);
            ChessPiece rook = (ChessPiece) board.removePiece(targetT);
            board.placePiece(rook, sourceT);
            rook.decreaseMoveCount();
        }
        // En Passant
        if (p instanceof Pawn) {
            if (source.getCol() != target.getCol() && captured == enPassantVulnerable) {
                ChessPiece pawn = (ChessPiece) board.removePiece(target);
                Position pawnPosition = new Position(
                        p.getColor() == Color.WHITE ? 3 : 4,
                        target.getCol());
                board.placePiece(pawn, pawnPosition);
            }
        }

        capturedPieces.remove(captured);
        if (captured != null) {
            piecesOnTheBoard.add(captured);
        }
    }

    private void validateSourcePosition(Position pos) {
        if (!board.isPiecePlaced(pos)) {
            throw new ChessException("Não existe peça na posição de origem.");
        }
        if (currentPlayer != ((ChessPiece) board.piece(pos)).getColor()) {
            throw new ChessException("A peça escolhida não é sua.");
        }
        if (!board.piece(pos).isThereAnyPossibleMove()) {
            throw new ChessException("Não existe movimentos possíveis para a peça escolhida.");
        }
    }

    /*@ private normal_behavior
      @   requires source != null;
      @   requires target != null;
      @   requires source.getRow() >= 0 && source.getRow() < 8;
      @   requires source.getCol() >= 0 && source.getCol() < 8;
      @   requires target.getRow() >= 0 && target.getRow() < 8;
      @   requires target.getCol() >= 0 && target.getCol() < 8;
      @   requires board.piece(source).possibleMove(target);
      @   assignable \nothing;
      @ also private exceptional_behavior
      @   requires source != null;
      @   requires target != null;
      @   requires !board.piece(source).possibleMove(target);
      @   assignable \nothing;
      @   signals_only ChessException;
      @   signals (ChessException e) true;
      @*/
    private void validateTargetPosition(/*@ non_null @*/ Position source,
            /*@ non_null @*/ Position target) {
        if (!board.piece(source).possibleMove(target)) {
            throw new ChessException("A peça escolhida não pode realizar esse movimento.");
        }
    }

    private void nextTurn() {
        turn++;
        currentPlayer = (currentPlayer == Color.WHITE) ? Color.BLACK : Color.WHITE;
    }

    private Color opponent(Color color) {
        return color == Color.WHITE ? Color.BLACK : Color.WHITE;
    }

    private ChessPiece king(Color color) {
        for (int i = 0; i < piecesOnTheBoard.size(); i++) {
            Piece p = piecesOnTheBoard.get(i);
            if (p != null && p instanceof ChessPiece) {
                ChessPiece cp = (ChessPiece) p;
                if (cp.getColor() == color && cp instanceof King) {
                    return cp;
                }
            }
        }
        throw new IllegalStateException("Não existe um rei " + color + " no tabuleiro.");
    }

    private boolean testCheck(Color color) {
        Position kingPos = king(color).getChessPosition().toPosition();

        for (int i = 0; i < piecesOnTheBoard.size(); i++) {
            Piece p = piecesOnTheBoard.get(i);
            if (p != null && p instanceof ChessPiece) {
                ChessPiece cp = (ChessPiece) p;
                if (cp.getColor() == opponent(color)) {
                    boolean[][] mat = p.possibleMoves();
                    if (mat != null && mat.length > kingPos.getRow() && 
                        mat[kingPos.getRow()] != null && 
                        mat[kingPos.getRow()].length > kingPos.getCol() &&
                        mat[kingPos.getRow()][kingPos.getCol()]) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    private boolean testCheckMate(Color color) {
        if (!testCheck(color)) return false;

        List<Piece> list = piecesOnTheBoard.stream()
                .filter(x -> x != null && x instanceof ChessPiece && ((ChessPiece) x).getColor() == color)
                .toList();
        for (Piece p : list) {
            boolean[][] mat = p.possibleMoves();
            if (mat == null) continue;
            for (int i = 0; i < board.getRows(); i++) {
                if (mat.length <= i || mat[i] == null) continue;
                for (int j = 0; j < board.getCols(); j++) {
                    if (mat[i].length <= j) continue;
                    if (mat[i][j]) {
                        Position source = ((ChessPiece) p).getChessPosition().toPosition();
                        Position target = new Position(i, j);
                        Piece captured = makeMove(source, target);
                        boolean test = testCheck(color);
                        undoMove(source, target, captured);

                        if (!test) {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }

    private void placeNewPiece(char col, int row, ChessPiece piece) {
        board.placePiece(piece, new ChessPosition(row, col).toPosition());
        piecesOnTheBoard.add(piece);
    }

    private void initialSetup() {
        // Peças brancas - primeira fileira
        placeNewPiece('a', 1, new Rook(board, Color.WHITE));
        placeNewPiece('b', 1, new Knight(board, Color.WHITE));
        placeNewPiece('c', 1, new Bishop(board, Color.WHITE));
        placeNewPiece('d', 1, new Queen(board, Color.WHITE));
        placeNewPiece('e', 1, new King(board, Color.WHITE, this));
        placeNewPiece('f', 1, new Bishop(board, Color.WHITE));
        placeNewPiece('g', 1, new Knight(board, Color.WHITE));
        placeNewPiece('h', 1, new Rook(board, Color.WHITE));

        // Peões brancos
        placeNewPiece('a', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('b', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('c', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('d', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('e', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('f', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('g', 2, new Pawn(board, Color.WHITE, this));
        placeNewPiece('h', 2, new Pawn(board, Color.WHITE, this));

        // Peças pretas - última fileira
        placeNewPiece('a', 8, new Rook(board, Color.BLACK));
        placeNewPiece('b', 8, new Knight(board, Color.BLACK));
        placeNewPiece('c', 8, new Bishop(board, Color.BLACK));
        placeNewPiece('d', 8, new Queen(board, Color.BLACK));
        placeNewPiece('e', 8, new King(board, Color.BLACK, this));
        placeNewPiece('f', 8, new Bishop(board, Color.BLACK));
        placeNewPiece('g', 8, new Knight(board, Color.BLACK));
        placeNewPiece('h', 8, new Rook(board, Color.BLACK));

        // Peões pretos
        placeNewPiece('a', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('b', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('c', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('d', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('e', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('f', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('g', 7, new Pawn(board, Color.BLACK, this));
        placeNewPiece('h', 7, new Pawn(board, Color.BLACK, this));
    }
}
