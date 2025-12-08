package chess;

import boardgame.Board;
import boardgame.Piece;
import boardgame.Position;
import chess.pieces.*;

import java.util.ArrayList;
import java.util.List;

/**
 * Classe que gerencia uma partida de xadrez completa.
 * Controla o tabuleiro, turnos, jogador atual, verificação de xeque e xeque-mate,
 * movimentos especiais (roque, en passant, promoção) e captura de peças.
 */
public class ChessMatch {

    //@ public invariant turn >= 1;
    //@ public invariant currentPlayer != null;
    //@ public invariant currentPlayer == Color.WHITE || currentPlayer == Color.BLACK;
    //@ public invariant board != null;
    //@ public invariant piecesOnTheBoard != null;
    //@ public invariant capturedPieces != null;
    //@ public invariant !checkMate ==> (currentPlayer == Color.WHITE || currentPlayer == Color.BLACK);
    //@ public invariant board.rows == 8 && board.cols == 8;

    //@ spec_public
    protected /*@ non_null @*/ Board board;

    //@ spec_public
    private int turn;

    //@ spec_public
    private /*@ non_null @*/ Color currentPlayer;

    //@ spec_public
    private boolean check;

    //@ spec_public
    private boolean checkMate;

    /*@ spec_public nullable @*/
    private ChessPiece enPassantVulnerable;

    /*@ spec_public nullable @*/
    private ChessPiece promoted;

    //@ spec_public
    private final /*@ non_null @*/ List<Piece> piecesOnTheBoard;

    //@ spec_public
    private final /*@ non_null @*/ List<Piece> capturedPieces;

    /*@ public behavior
      @   ensures board != null;
      @   ensures board.getRows() == 8;
      @   ensures board.getCols() == 8;
      @   ensures turn == 1;
      @   ensures currentPlayer == Color.WHITE;
      @   ensures !check;
      @   ensures !checkMate;
      @   ensures enPassantVulnerable == null;
      @   ensures promoted == null;
      @   ensures piecesOnTheBoard != null;
      @   ensures capturedPieces != null;
      @   ensures piecesOnTheBoard.size() == 32;
      @   ensures capturedPieces.size() == 0;
      @*/
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

    /*@ public behavior
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @   assignable \nothing;
      @*/
    public /*@ pure non_null @*/ ChessPiece[][] getPieces() {
        final int rows = board.getRows();
        final int cols = board.getCols();

        ChessPiece[][] mat = new ChessPiece[rows][];

        /*@ loop_invariant 0 <= i && i <= rows;
          @ loop_invariant mat.length == rows;
          @ loop_invariant (\forall int k; 0 <= k && k < i;
          @                     mat[k] != null && mat[k].length == cols);
          @ decreases rows - i;
          @*/
        for (int i = 0; i < rows; i++) {

            ChessPiece[] rowArray = new ChessPiece[cols];
            mat[i] = rowArray;

            /*@ loop_invariant 0 <= j && j <= cols;
              @ loop_invariant rowArray.length == cols;
              @ decreases cols - j;
              @*/
            for (int j = 0; j < cols; j++) {
                /*@ nullable @*/ Piece p = board.piece(i, j);

                if (p != null && p instanceof ChessPiece c) {
                    rowArray[j] = c;
                }
            }
        }

        return mat;
    }

    /*@ public normal_behavior
      @   ensures \result == turn;
      @   ensures \result >= 1;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ int getTurn() {
        return turn;
    }

    /*@ public normal_behavior
      @   ensures \result == currentPlayer;
      @   ensures \result != null;
      @   ensures \result == Color.WHITE || \result == Color.BLACK;
      @   assignable \nothing;
      @*/
    public /*@ pure non_null @*/ Color getCurrentPlayer() {
        return currentPlayer;
    }

    /*@ public normal_behavior
      @   ensures \result == check;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean getCheck() {
        return check;
    }

    /*@ public normal_behavior
      @   ensures \result == !checkMate;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean getNotCheckMate() {
        return !checkMate;
    }

    /*@ public normal_behavior
      @   ensures \result == checkMate;
      @   assignable \nothing;
      @*/
    public /*@ pure @*/ boolean isCheckMate() {
        return checkMate;
    }

    /*@ public normal_behavior
      @   ensures \result == enPassantVulnerable;
      @   assignable \nothing;
      @*/
    public /*@ pure nullable @*/ ChessPiece getEnPassantVulnerable() {
        return enPassantVulnerable;
    }

    /*@ public normal_behavior
      @   ensures \result == promoted;
      @   assignable \nothing;
      @*/
    public /*@ pure nullable @*/ ChessPiece getPromoted() {
        return promoted;
    }

    /*@ public normal_behavior
      @   requires sourcePos != null;
      @   ensures \result != null;
      @   ensures \result.length == 8;
      @   ensures (\forall int i; 0 <= i && i < 8;
      @               \result[i] != null && \result[i].length == 8);
      @   assignable \nothing;
      @ also public exceptional_behavior
      @   requires sourcePos != null;
      @   assignable \nothing;
      @   signals_only ChessException;
      @   signals (ChessException e) true;
      @*/
    public boolean[][] possibleMoves(/*@ non_null @*/ ChessPosition sourcePos) {
        Position position = sourcePos.toPosition();
        validateSourcePosition(position);
        return board.piece(position).possibleMoves();
    }

    /*@ public normal_behavior
      @   requires sourcePos != null;
      @   requires targetPos != null;
      @   ensures turn >= \old(turn);
      @   ensures currentPlayer != null;
      @   assignable board, turn, currentPlayer, check, checkMate,
      @              enPassantVulnerable, promoted, piecesOnTheBoard, capturedPieces;
      @ also public exceptional_behavior
      @   requires sourcePos != null;
      @   requires targetPos != null;
      @   assignable board, turn, currentPlayer, check, checkMate,
      @              enPassantVulnerable, promoted, piecesOnTheBoard, capturedPieces;
      @   signals_only ChessException;
      @   signals (ChessException e) true;
      @*/
    public /*@ nullable @*/ ChessPiece performChessMove(/*@ non_null @*/ ChessPosition sourcePos,
            /*@ non_null @*/ ChessPosition targetPos) {
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

    /*@ public normal_behavior
      @   requires type != null;
      @   requires promoted != null;
      @   requires type.equals("B") || type.equals("N") || type.equals("R") || type.equals("Q");
      @   ensures \result != null;
      @   ensures \result.getColor() == \old(promoted).getColor();
      @   assignable board, piecesOnTheBoard, promoted;
      @ also public normal_behavior
      @   requires type != null;
      @   requires promoted != null;
      @   requires !type.equals("B") && !type.equals("N") && !type.equals("R") && !type.equals("Q");
      @   ensures \result == promoted;
      @   assignable \nothing;
      @ also public exceptional_behavior
      @   requires promoted == null;
      @   assignable \nothing;
      @   signals_only IllegalStateException;
      @   signals (IllegalStateException e) true;
      @*/
    public /*@ non_null @*/ ChessPiece replacePromotedPiece(/*@ non_null @*/ String type) {
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

    /*@ private normal_behavior
      @   requires type != null;
      @   requires color != null;
      @   requires type.equals("B") || type.equals("N") || type.equals("Q") || type.equals("R");
      @   ensures \result != null;
      @   ensures \result.getColor() == color;
      @   ensures type.equals("B") ==> \result instanceof Bishop;
      @   ensures type.equals("N") ==> \result instanceof Knight;
      @   ensures type.equals("Q") ==> \result instanceof Queen;
      @   ensures type.equals("R") ==> \result instanceof Rook;
      @   assignable \nothing;
      @*/
    private /*@ pure non_null @*/ ChessPiece newPiece(/*@ non_null @*/ String type,
            /*@ non_null @*/ Color color) {
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

    /*@ private normal_behavior
      @   requires source != null;
      @   requires target != null;
      @   requires source.getRow() >= 0 && source.getRow() < 8;
      @   requires source.getCol() >= 0 && source.getCol() < 8;
      @   requires target.getRow() >= 0 && target.getRow() < 8;
      @   requires target.getCol() >= 0 && target.getCol() < 8;
      @   requires board.isPiecePlaced(source);
      @   ensures board.isPiecePlaced(target);
      @   ensures !board.isPiecePlaced(source);
      @   assignable board, piecesOnTheBoard, capturedPieces;
      @*/
    private /*@ nullable @*/ Piece makeMove(/*@ non_null @*/ Position source,
            /*@ non_null @*/ Position target) {
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

    /*@ private normal_behavior
      @   requires source != null;
      @   requires target != null;
      @   requires source.getRow() >= 0 && source.getRow() < 8;
      @   requires source.getCol() >= 0 && source.getCol() < 8;
      @   requires target.getRow() >= 0 && target.getRow() < 8;
      @   requires target.getCol() >= 0 && target.getCol() < 8;
      @   requires board.isPiecePlaced(target);
      @   ensures board.isPiecePlaced(source);
      @   ensures captured != null ==> board.isPiecePlaced(target);
      @   assignable board, piecesOnTheBoard, capturedPieces;
      @*/
    private void undoMove(/*@ non_null @*/ Position source,
            /*@ non_null @*/ Position target,
            /*@ nullable @*/ Piece captured) {
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

    /*@ private normal_behavior
      @   requires pos != null;
      @   requires pos.getRow() >= 0 && pos.getRow() < 8;
      @   requires pos.getCol() >= 0 && pos.getCol() < 8;
      @   requires board.isPiecePlaced(pos);
      @   requires ((ChessPiece)board.piece(pos)).getColor() == currentPlayer;
      @   requires board.piece(pos).isThereAnyPossibleMove();
      @   assignable \nothing;
      @ also private exceptional_behavior
      @   requires pos != null;
      @   requires !board.isPiecePlaced(pos) ||
      @            ((ChessPiece)board.piece(pos)).getColor() != currentPlayer ||
      @            !board.piece(pos).isThereAnyPossibleMove();
      @   assignable \nothing;
      @   signals_only ChessException;
      @   signals (ChessException e) true;
      @*/
    private void validateSourcePosition(/*@ non_null @*/ Position pos) {
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

    /*@ private normal_behavior
      @   requires turn < Integer.MAX_VALUE;
      @   ensures turn == \old(turn) + 1;
      @   ensures currentPlayer == (\old(currentPlayer) == Color.WHITE ? Color.BLACK : Color.WHITE);
      @   ensures currentPlayer != \old(currentPlayer);
      @   assignable turn, currentPlayer;
      @*/
    private void nextTurn() {
        turn++;
        currentPlayer = (currentPlayer == Color.WHITE) ? Color.BLACK : Color.WHITE;
    }

    /*@ private normal_behavior
      @   requires color != null;
      @   ensures \result != null;
      @   ensures \result == (color == Color.WHITE ? Color.BLACK : Color.WHITE);
      @   ensures \result != color;
      @   assignable \nothing;
      @*/
    private /*@ pure non_null @*/ Color opponent(/*@ non_null @*/ Color color) {
        return color == Color.WHITE ? Color.BLACK : Color.WHITE;
    }

    /*@ private normal_behavior
      @   requires color != null;
      @   ensures \result != null;
      @   ensures \result instanceof King;
      @   ensures \result.getColor() == color;
      @   assignable \nothing;
      @ also private exceptional_behavior
      @   requires color != null;
      @   assignable \nothing;
      @   signals_only IllegalStateException;
      @   signals (IllegalStateException e) true;
      @*/
    private /*@ non_null @*/ ChessPiece king(/*@ non_null @*/ Color color) {
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

    /*@ private normal_behavior
      @   requires color != null;
      @   ensures \result == true ==> (\exists Piece opp;
      @               piecesOnTheBoard.contains(opp) &&
      @               ((ChessPiece)opp).getColor() != color;
      @               opp.possibleMoves()[king(color).getChessPosition().toPosition().getRow()]
      @                                  [king(color).getChessPosition().toPosition().getCol()]);
      @   assignable \nothing;
      @*/
    private /*@ pure @*/ boolean testCheck(/*@ non_null @*/ Color color) {
        Position kingPos = king(color).getChessPosition().toPosition();

        for (int i = 0; i < piecesOnTheBoard.size(); i++) {
            Piece p = piecesOnTheBoard.get(i);
            if (p != null && p instanceof ChessPiece) {
                ChessPiece cp = (ChessPiece) p;
                if (cp.getColor() == opponent(color)) {
                    boolean[][] mat = p.possibleMoves();
                    if (mat[kingPos.getRow()][kingPos.getCol()]) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /*@ private normal_behavior
      @   requires color != null;
      @   ensures \result == true ==> testCheck(color);
      @   ensures \result == true ==> (\forall Piece piece;
      @               piecesOnTheBoard.contains(piece) &&
      @               ((ChessPiece)piece).getColor() == color;
      @               (\forall int i, j; 0 <= i && i < 8 && 0 <= j && j < 8 &&
      @                   piece.possibleMoves()[i][j];
      @                   testCheck(color)));
      @   assignable board, piecesOnTheBoard, capturedPieces;
      @*/
    private boolean testCheckMate(/*@ non_null @*/ Color color) {
        if (!testCheck(color)) return false;

        List<Piece> list = piecesOnTheBoard.stream()
                .filter(x -> x != null && ((ChessPiece) x).getColor() == color)
                .toList();
        for (Piece p : list) {
            boolean[][] mat = p.possibleMoves();
            for (int i = 0; i < board.getRows(); i++) {
                for (int j = 0; j < board.getCols(); j++) {
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

    /*@ private normal_behavior
      @   requires piece != null;
      @   requires col >= 'a' && col <= 'h';
      @   requires row >= 1 && row <= 8;
      @   ensures piecesOnTheBoard.contains(piece);
      @   ensures board.piece(8 - row, col - 'a') == piece;
      @   assignable board, piecesOnTheBoard;
      @*/
    private void placeNewPiece(char col, int row, /*@ non_null @*/ ChessPiece piece) {
        board.placePiece(piece, new ChessPosition(row, col).toPosition());
        piecesOnTheBoard.add(piece);
    }

    /*@ skipesc @*/
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
