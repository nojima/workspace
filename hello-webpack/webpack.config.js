const path = require("path");
const HtmlWebpackPlugin = require("html-webpack-plugin");
const { CleanWebpackPlugin } = require("clean-webpack-plugin");

module.exports = {
    entry: "./src/index.ts",
    plugins: [
        new CleanWebpackPlugin(),
        new HtmlWebpackPlugin({
            title: "TypeScript",
        }),
    ],
    output: {
        filename: "bundle.js",
        path: path.resolve(__dirname, "dist"),
    },
    module: {
        rules: [
            {
                test: /\.css$/,
                use: [
                    "style-loader",
                    "css-loader",
                ],
            },
            {
                test: /\.(png|svg|jpe?g|gif)$/,
                use: [
                    "file-loader",
                ],
            },
            {
                test: "/\.tsx?$/",
                use: "ts-loader",
                exclude: /node_modules/,
            },
        ],
    },
    resolve: {
        extensions: [".tsx", ".ts", ".js"],
    },
};
