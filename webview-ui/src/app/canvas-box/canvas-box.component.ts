import { Component, OnInit } from '@angular/core';
import * as THREE from 'three';
import {OrbitControls} from 'three/examples/jsm/controls/OrbitControls.js';
import ThreeForceGraph from 'three-forcegraph';
import data from '../data.json';
import { animate } from '@angular/animations';
import SpriteText from 'three-spritetext';

@Component({
  selector: 'app-canvas-box',
  templateUrl: './canvas-box.component.html',
  styleUrls: ['./canvas-box.component.css']
})
export class CanvasBoxComponent implements OnInit {

    // The color of the sphere.
    color: THREE.ColorRepresentation = 0x000000;

    // The sphere in the scene.
    sphere!: THREE.Mesh<THREE.SphereGeometry, THREE.MeshBasicMaterial>;

    // The plane in the scene.
    plane!: THREE.Mesh<THREE.PlaneGeometry, THREE.MeshBasicMaterial>;

    // Canvas that WebGL draws on.
    canvas!: HTMLElement | null;

    // WebGL Renderer.
    renderer!: THREE.WebGLRenderer;

    // The scene.
    scene!: THREE.Scene;

    // The camera that captures the scene.
    camera!: THREE.PerspectiveCamera;

    // Orbit controls allow controlling the camera.
    orbit!: OrbitControls;

    // Constructor.
    constructor() {
    }

    //On Initialization of the component.
    ngOnInit(): void {
        this.canvas = document.getElementById('canvas-box');
        this.renderer = new THREE.WebGLRenderer({ antialias: true, canvas: this.canvas!,});
        this.renderer.setSize(window.innerWidth, window.innerHeight);
        this.scene = new THREE.Scene();
        this.scene.add(new THREE.AmbientLight(0xbbbbbb));
        this.camera = new THREE.PerspectiveCamera(
            50,
            window.innerWidth / window.innerHeight,
            0.1,
            10000
          );
        this.camera.position.z = Math.cbrt(2) * 180;

        const graph = new ThreeForceGraph().graphData(data);
        graph.numDimensions(2);
        graph.nodeThreeObjectExtend(true);

        // const map = data.nodes.map(({name, val, id}) => {
        //     const sprite = new SpriteText(name)
        //     sprite.textHeight = 6;
        //     sprite.position.y = -8
        //     return sprite
        // })

        const map = new Map(data.nodes.map((obj)=>[obj.id, obj.name]))


        graph.nodeThreeObject(node=>{
            if (typeof node.id == "string"){
                const sprite = new SpriteText(map.get(node.id))
                sprite.textHeight = 6;
                sprite.position.y = -8
                return sprite
            }
            else {
                const sprite = new SpriteText("N/A")
                sprite.textHeight = 6;
                sprite.position.y = -8
                return sprite
            }
        });
        this.scene.add(graph);
        this.camera.lookAt(graph.position);
        
          const animateGeometry = () => {

            graph.tickFrame();
            this.renderer.render(this.scene, this.camera);

            // Call animateGeometry again on the next frame.
            window.requestAnimationFrame(animateGeometry);
        };

        animateGeometry();
    }
}
