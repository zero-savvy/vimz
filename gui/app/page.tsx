'use client'

import { useState, useRef, useEffect } from 'react'
import { Button } from "@/components/ui/button"
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card"
import { Input } from "@/components/ui/input"
import { Slider } from "@/components/ui/slider"
import { Upload, Download, ImageIcon } from 'lucide-react'

export default function ImageEditor() {
  const [originalImage, setOriginalImage] = useState<string | null>(null)
  const [displayedImage, setDisplayedImage] = useState<string | null>(null)
  const [editedFullSizeImage, setEditedFullSizeImage] = useState<string | null>(null)
  const [imageHistory, setImageHistory] = useState<string[]>([])
  const canvasRef = useRef<HTMLCanvasElement>(null)

  const resizeImageForDisplay = (img: HTMLImageElement, maxWidth: number, maxHeight: number): string => {
    const canvas = document.createElement('canvas')
    const ctx = canvas.getContext('2d')!
    let width = img.width
    let height = img.height

    if (width > height) {
      if (width > maxWidth) {
        height *= maxWidth / width
        width = maxWidth
      }
    } else {
      if (height > maxHeight) {
        width *= maxHeight / height
        height = maxHeight
      }
    }

    canvas.width = width
    canvas.height = height
    ctx.drawImage(img, 0, 0, width, height)
    return canvas.toDataURL()
  }

  const handleImageUpload = (e: React.ChangeEvent<HTMLInputElement>) => {
    if (e.target.files && e.target.files[0]) {
      const file = e.target.files[0]
      const reader = new FileReader()
      reader.onload = (event) => {
        const img = new Image()
        img.onload = () => {
          setOriginalImage(event.target?.result as string)
          const resizedImage = resizeImageForDisplay(img, 600, 600)
          setDisplayedImage(resizedImage)
          setEditedFullSizeImage(event.target?.result as string)
          setImageHistory([event.target?.result as string])
        }
        img.src = event.target?.result as string
      }
      reader.readAsDataURL(file)
    }
  }

  const applyImageEffect = (effect: string, value?: number) => {
    if (!originalImage) return

    const canvas = document.createElement('canvas')
    const ctx = canvas.getContext('2d')!
    const img = new Image()

    img.onload = () => {
      canvas.width = img.width
      canvas.height = img.height
      ctx.drawImage(img, 0, 0)
      const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height)
      const data = imageData.data

      switch (effect) {
        case 'grayscale':
          for (let i = 0; i < data.length; i += 4) {
            const avg = (data[i] + data[i + 1] + data[i + 2]) / 3
            data[i] = data[i + 1] = data[i + 2] = avg
          }
          break
        case 'blur':
          // Simple box blur
          const tempData = new Uint8ClampedArray(data)
          for (let y = 1; y < canvas.height - 1; y++) {
            for (let x = 1; x < canvas.width - 1; x++) {
              for (let c = 0; c < 3; c++) {
                const i = (y * canvas.width + x) * 4 + c
                data[i] = (tempData[i - 4] + tempData[i - canvas.width * 4] + tempData[i + 4] + tempData[i + canvas.width * 4] + tempData[i]) / 5
              }
            }
          }
          break
        case 'sharpen':
          // Simple sharpening
          const tempData2 = new Uint8ClampedArray(data)
          for (let y = 1; y < canvas.height - 1; y++) {
            for (let x = 1; x < canvas.width - 1; x++) {
              for (let c = 0; c < 3; c++) {
                const i = (y * canvas.width + x) * 4 + c
                data[i] = Math.min(255, Math.max(0, 5 * tempData2[i] - tempData2[i - 4] - tempData2[i - canvas.width * 4] - tempData2[i + 4] - tempData2[i + canvas.width * 4]))
              }
            }
          }
          break
        case 'contrast':
          const factor = (259 * (value! + 255)) / (255 * (259 - value!))
          for (let i = 0; i < data.length; i += 4) {
            data[i] = factor * (data[i] - 128) + 128
            data[i + 1] = factor * (data[i + 1] - 128) + 128
            data[i + 2] = factor * (data[i + 2] - 128) + 128
          }
          break
      }

      ctx.putImageData(imageData, 0, 0)
      const newFullSizeImage = canvas.toDataURL()
      setEditedFullSizeImage(newFullSizeImage)
      setImageHistory(prev => [...prev, newFullSizeImage])

      // Create a resized version for display
      const displayImg = new Image()
      displayImg.onload = () => {
        const resizedImage = resizeImageForDisplay(displayImg, 600, 600)
        setDisplayedImage(resizedImage)
      }
      displayImg.src = newFullSizeImage
    }
    img.src = editedFullSizeImage || originalImage
  }

  const handleDownload = () => {
    if (editedFullSizeImage) {
      const link = document.createElement('a')
      link.href = editedFullSizeImage
      link.download = 'edited_image_full_size.png'
      link.click()

      const jsonData = JSON.stringify(imageHistory)
      const blob = new Blob([jsonData], { type: 'application/json' })
      const url = URL.createObjectURL(blob)
      const jsonLink = document.createElement('a')
      jsonLink.href = url
      jsonLink.download = 'image_history.json'
      jsonLink.click()
      URL.revokeObjectURL(url)
    }
  }

  return (
    <div className="min-h-screen bg-gray-100 p-4 font-sans">
      <div className="container mx-auto">
        <h1 className="text-4xl font-bold mb-8 text-center text-gray-800">Image Editor</h1>
        <Card className="bg-white shadow-xl">
          <CardHeader>
            <CardTitle className="text-2xl text-gray-700 flex items-center gap-2">
              <ImageIcon className="w-6 h-6" />
              Edit Image
            </CardTitle>
          </CardHeader>
          <CardContent>
            <div className="space-y-6">
              <div className="relative">
                <Input type="file" accept="image/*" onChange={handleImageUpload} className="sr-only" id="image-upload" />
                <label htmlFor="image-upload" className="flex items-center justify-center w-full h-12 px-4 transition-colors duration-150 bg-blue-600 rounded-lg hover:bg-blue-700 focus:shadow-outline cursor-pointer text-white">
                  <Upload className="w-5 h-5 mr-2" />
                  <span>Upload Image</span>
                </label>
              </div>
              {displayedImage && (
                <div className="space-y-4">
                  <div className="border-2 border-gray-300 p-2">
                    <img src={displayedImage} alt="Edited" className="mx-auto max-w-full h-auto" />
                  </div>
                  <div className="grid grid-cols-2 sm:grid-cols-3 gap-4">
                    <Button onClick={() => applyImageEffect('grayscale')} className="bg-gray-700 hover:bg-gray-600 text-white">
                      Grayscale
                    </Button>
                    <Button onClick={() => applyImageEffect('blur')} className="bg-blue-700 hover:bg-blue-600 text-white">
                      Blur
                    </Button>
                    <Button onClick={() => applyImageEffect('sharpen')} className="bg-green-700 hover:bg-green-600 text-white">
                      Sharpen
                    </Button>
                  </div>
                  <div className="space-y-2">
                    <label className="text-sm font-medium text-gray-700">Contrast</label>
                    <Slider
                      defaultValue={[0]}
                      max={100}
                      step={1}
                      onValueChange={(value) => applyImageEffect('contrast', value[0])}
                    />
                  </div>
                  <div className="grid grid-cols-2 gap-4">
                    <Button onClick={handleDownload} className="bg-purple-700 hover:bg-purple-600 text-white">
                      <Download className="w-4 h-4 mr-2" />
                      Download
                    </Button>
                  </div>
                </div>
              )}
            </div>
          </CardContent>
        </Card>
      </div>
      <canvas ref={canvasRef} style={{ display: 'none' }} />
    </div>
  )
}