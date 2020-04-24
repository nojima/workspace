import React from "react";
import ReactDOM from "react-dom";
import { List } from "immutable";
import "./index.css";

function Square(props) {
    return (
        <button className="square" onClick={props.onClick}>
            {props.value}
        </button>
    );
}

function nextTurn(current) {
    return current === 'X' ? 'O' : 'X';
}

function calculateWinner(squares) {
    const lines = [
        [0, 1, 2],
        [3, 4, 5],
        [6, 7, 8],
        [0, 3, 6],
        [1, 4, 7],
        [2, 5, 8],
        [0, 4, 8],
        [2, 4, 6],
    ];
    for (let i = 0; i < lines.length; i++) {
        const [a, b, c] = lines[i];
        if (squares.get(a) && squares.get(a) === squares.get(b) && squares.get(a) === squares.get(c)) {
            return squares.get(a);
        }
    }
    return null;
}

class Board extends React.Component {
    constructor(props) {
        super(props);
        this.state = {
            squares: List(Array(9).fill(null)),
            turn: 'X',
        };
    }

    handleClick(i) {
        const squares = this.state.squares;
        this.setState({
            squares: squares.set(i, this.state.turn),
            turn: nextTurn(this.state.turn),
        });
    }

    renderSquare(i) {
        return (
            <Square
                value={this.state.squares.get(i)}
                onClick={() => this.handleClick(i)}
            />
        );
    }

    render() {
        const winner = calculateWinner(this.state.squares);
        let status;
        if (winner) {
            status = "Winner: " + winner;
        } else {
            status = "Next player: " + this.state.turn;
        }

        return (
            <div>
                <div className="status">{status}</div>
                <div className="board-row">
                    {this.renderSquare(0)}
                    {this.renderSquare(1)}
                    {this.renderSquare(2)}
                </div>
                <div className="board-row">
                    {this.renderSquare(3)}
                    {this.renderSquare(4)}
                    {this.renderSquare(5)}
                </div>
                <div className="board-row">
                    {this.renderSquare(6)}
                    {this.renderSquare(7)}
                    {this.renderSquare(8)}
                </div>
            </div>
        );
    }
}

class Game extends React.Component {
    render() {
        return (
            <div className="game">
                <div className="game-board">
                    <Board />
                </div>
                <div className="game-info">
                    <div>{/* status */}</div>
                    <ol>{/* TODO */}</ol>
                </div>
            </div>
        );
    }
}

// ============================================================================

ReactDOM.render(
    <Game />,
    document.getElementById("root")
);
