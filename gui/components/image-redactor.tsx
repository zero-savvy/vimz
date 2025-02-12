"use client"

import type React from "react"
import { useState, useRef, useEffect } from "react"
import { Button } from "@/components/ui/button"
import { Card, CardContent } from "@/components/ui/card"
import { Label } from "@/components/ui/label"
import { Input } from "@/components/ui/input"

const ImageRedactor: React.FC = () => {
  const [image, setImage] = useState<HTMLImageElement | null>(null)
  const [selectedBlocks, setSelectedBlocks] = useState<boolean[][]>([])
  const [imageData, setImageData] = useState<string[][][]>([])
  const canvasRef = useRef<HTMLCanvasElement>(null)

  const BLOCK_SIZE = 32

  useEffect(() => {
    if (image && canvasRef.current) {
      const canvas = canvasRef.current
      const ctx = canvas.getContext("2d")
      if (ctx) {
        canvas.width = image.width
        canvas.height = image.height
        ctx.drawImage(image, 0, 0)

        const blocksX = Math.ceil(image.width / BLOCK_SIZE)
        const blocksY = Math.ceil(image.height / BLOCK_SIZE)

        // Initialize selectedBlocks
        setSelectedBlocks(
          Array(blocksY)
            .fill(null)
            .map(() => Array(blocksX).fill(false)),
        )

        // Process image data
        const newImageData: string[][][] = []
        for (let y = 0; y < blocksY; y++) {
          const row: string[][] = []
          for (let x = 0; x < blocksX; x++) {
            const blockData: string[] = []
            for (let i = 0; i < 128; i++) {
              let hexString = ""
              for (let j = 0; j < 8; j++) {
                const pixelX = x * BLOCK_SIZE + j
                const pixelY = y * BLOCK_SIZE + i
                if (pixelX < image.width && pixelY < image.height) {
                  const data = ctx.getImageData(pixelX, pixelY, 1, 1).data
                  hexString += data[0].toString(16).padStart(2, "0")
                  hexString += data[1].toString(16).padStart(2, "0")
                  hexString += data[2].toString(16).padStart(2, "0")
                } else {
                  hexString += "000000" // Padding for out-of-bounds pixels
                }
              }
              blockData.push(hexString)
            }
            row.push(blockData)
          }
          newImageData.push(row)
        }
        setImageData(newImageData)
      }
    }
  }, [image])

  const handleImageUpload = (e: React.ChangeEvent<HTMLInputElement>) => {
    const file = e.target.files?.[0]
    if (file) {
      const reader = new FileReader()
      reader.onload = (event) => {
        const img = new Image()
        img.onload = () => setImage(img)
        img.src = event.target?.result as string
      }
      reader.readAsDataURL(file)
    }
  }

  const handleCanvasClick = (e: React.MouseEvent<HTMLCanvasElement>) => {
    if (canvasRef.current && image) {
      const canvas = canvasRef.current
      const rect = canvas.getBoundingClientRect()
      const scaleX = image.width / rect.width
      const scaleY = image.height / rect.height

      const x = Math.floor(((e.clientX - rect.left) * scaleX) / BLOCK_SIZE)
      const y = Math.floor(((e.clientY - rect.top) * scaleY) / BLOCK_SIZE)

      setSelectedBlocks((prev) => {
        const newBlocks = [...prev]
        newBlocks[y][x] = !newBlocks[y][x]
        return newBlocks
      })

      const ctx = canvas.getContext("2d")
      if (ctx) {
        if (!selectedBlocks[y][x]) {
          ctx.fillStyle = "black" // Solid black
          ctx.fillRect(x * BLOCK_SIZE, y * BLOCK_SIZE, BLOCK_SIZE, BLOCK_SIZE)
        } else {
          ctx.drawImage(
            image,
            x * BLOCK_SIZE,
            y * BLOCK_SIZE,
            BLOCK_SIZE,
            BLOCK_SIZE,
            x * BLOCK_SIZE,
            y * BLOCK_SIZE,
            BLOCK_SIZE,
            BLOCK_SIZE,
          )
        }
      }
    }
  }

  const handleDownload = () => {
    if (canvasRef.current && image) {
      // Download redacted image
      const link = document.createElement("a")
      link.download = "redacted_image.png"
      link.href = canvasRef.current.toDataURL()
      link.click()

      // Download JSON file
      const jsonContent = JSON.stringify({
        selectedBlocks,
        imageData,
      })
      const blob = new Blob([jsonContent], { type: "application/json" })
      const url = URL.createObjectURL(blob)
      const jsonLink = document.createElement("a")
      jsonLink.download = "image_data.json"
      jsonLink.href = url
      jsonLink.click()
      URL.revokeObjectURL(url)
    }
  }

  return (
    <Card className="w-full max-w-3xl mx-auto">
      <CardContent className="p-6">
        <div className="mb-4">
          <Label htmlFor="image-upload">Upload Image</Label>
          <Input id="image-upload" type="file" accept="image/*" onChange={handleImageUpload} className="mt-1" />
        </div>
        {image && (
          <div className="space-y-4">
            <div className="border rounded-lg overflow-auto" style={{ maxHeight: "70vh" }}>
              <canvas ref={canvasRef} onClick={handleCanvasClick} style={{ cursor: "pointer" }} />
            </div>
            <Button onClick={handleDownload} className="w-full">
              Download Redacted Image and JSON
            </Button>
          </div>
        )}
      </CardContent>
    </Card>
  )
}

export default ImageRedactor

