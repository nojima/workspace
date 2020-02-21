import _ from "lodash";
import "./style.css";
//import Zelda from "./zelda.jpg";

function component() {
    const element = document.createElement("div");

    element.innerHTML = _.join(["Hello", "webpack"], " ");
    element.classList.add("hello");

    // Add the image to our existing div.
    //const myImage = new Image();
    //myImage.src = Zelda;

    //element.appendChild(myImage);

    return element;
}

document.body.appendChild(component());
